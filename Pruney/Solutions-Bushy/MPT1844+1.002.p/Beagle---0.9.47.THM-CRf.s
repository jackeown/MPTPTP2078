%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1844+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:31 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 122 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 273 expanded)
%              Number of equality atoms :    4 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_30,axiom,(
    ! [A] :
      ( ~ v1_zfmisc_1(A)
     => ~ v1_xboole_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_realset1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(f_70,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tex_2)).

tff(c_24,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_35,plain,(
    ! [A_19,B_20] :
      ( k6_domain_1(A_19,B_20) = k1_tarski(B_20)
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_39,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_40,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(A_1)
      | v1_zfmisc_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_29,plain,(
    ! [A_17] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v7_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_33,plain,(
    ! [A_17] :
      ( ~ l1_struct_0(A_17)
      | v7_struct_0(A_17)
      | ~ v1_xboole_0(u1_struct_0(A_17)) ) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_43,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_33])).

tff(c_46,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_46])).

tff(c_50,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_49,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_18,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_51,plain,(
    ~ v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_18])).

tff(c_56,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k6_domain_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_56])).

tff(c_65,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_66,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_65])).

tff(c_71,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(B_23)
      | v1_subset_1(B_23,A_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_2'))
    | v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_71])).

tff(c_80,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_51,c_74])).

tff(c_12,plain,(
    ! [A_10] : v1_zfmisc_1(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_90,plain,(
    ! [B_27,A_28] :
      ( v1_subset_1(B_27,A_28)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | v1_zfmisc_1(A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_2'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_90])).

tff(c_99,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_100,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_80,c_51,c_99])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v7_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_107,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_107])).

%------------------------------------------------------------------------------
