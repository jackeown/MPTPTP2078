%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1145+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:29 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   46 (  74 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r7_relat_2 > r1_tarski > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( ( v6_orders_2(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => ( v6_orders_2(C,A)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_orders_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r7_relat_2(C,A)
          & r1_tarski(B,A) )
       => r7_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_orders_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12])).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ! [B_26,A_27] :
      ( v6_orders_2(B_26,A_27)
      | ~ r7_relat_2(u1_orders_2(A_27),B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_76,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).

tff(c_77,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_76])).

tff(c_26,plain,(
    ! [A_18] :
      ( m1_subset_1(u1_orders_2(A_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18),u1_struct_0(A_18))))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_relat_1(u1_orders_2(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_20,plain,(
    v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,(
    ! [A_24,B_25] :
      ( r7_relat_2(u1_orders_2(A_24),B_25)
      | ~ v6_orders_2(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_46,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_40])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [C_20,B_21,A_22] :
      ( r7_relat_2(C_20,B_21)
      | ~ r1_tarski(B_21,A_22)
      | ~ r7_relat_2(C_20,A_22)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_35,plain,(
    ! [C_20] :
      ( r7_relat_2(C_20,'#skF_3')
      | ~ r7_relat_2(C_20,'#skF_2')
      | ~ v1_relat_1(C_20) ) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

tff(c_53,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_35])).

tff(c_54,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_57,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_57])).

tff(c_62,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_62])).

%------------------------------------------------------------------------------
