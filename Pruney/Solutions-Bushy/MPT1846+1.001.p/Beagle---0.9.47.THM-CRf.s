%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1846+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   39 (  68 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 181 expanded)
%              Number of equality atoms :    6 (  25 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => ( v1_subset_1(C,u1_struct_0(A))
                  <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_18,plain,
    ( ~ v1_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_29,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_16,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_24])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    ! [B_21,A_22] :
      ( v1_subset_1(u1_struct_0(B_21),u1_struct_0(A_22))
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v1_tex_2(B_21,A_22)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [A_22] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_22))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v1_tex_2('#skF_3',A_22)
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41])).

tff(c_50,plain,(
    ! [A_23] :
      ( v1_subset_1('#skF_4',u1_struct_0(A_23))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v1_tex_2('#skF_3',A_23)
      | ~ m1_pre_topc('#skF_3',A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_53,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_59,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_30,c_53])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_59])).

tff(c_62,plain,(
    ~ v1_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_63,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_66,plain,(
    ! [B_24,A_25] :
      ( u1_struct_0(B_24) = '#skF_1'(A_25,B_24)
      | v1_tex_2(B_24,A_25)
      | ~ m1_pre_topc(B_24,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_62])).

tff(c_72,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_10,c_69])).

tff(c_77,plain,(
    ! [A_26,B_27] :
      ( ~ v1_subset_1('#skF_1'(A_26,B_27),u1_struct_0(A_26))
      | v1_tex_2(B_27,A_26)
      | ~ m1_pre_topc(B_27,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_77])).

tff(c_85,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_63,c_80])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_85])).

%------------------------------------------------------------------------------
