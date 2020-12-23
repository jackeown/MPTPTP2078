%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1844+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:31 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_30,axiom,(
    ! [A] :
      ( ~ v1_zfmisc_1(A)
     => ~ v1_xboole_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_realset1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_xboole_0(B)
           => v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_subset_1)).

tff(f_76,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( ~ v1_xboole_0(B)
              & v1_subset_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tex_2)).

tff(c_26,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_37,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_41,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_43,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(A_1)
      | v1_zfmisc_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_31,plain,(
    ! [A_18] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v7_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_35,plain,(
    ! [A_18] :
      ( ~ l1_struct_0(A_18)
      | v7_struct_0(A_18)
      | ~ v1_xboole_0(u1_struct_0(A_18)) ) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

tff(c_46,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_43,c_35])).

tff(c_52,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_52])).

tff(c_56,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_55,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_20,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_57,plain,(
    ~ v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_20])).

tff(c_62,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k6_domain_1(A_23,B_24),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_62])).

tff(c_71,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_72,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_71])).

tff(c_77,plain,(
    ! [B_25,A_26] :
      ( v1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_77])).

tff(c_86,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_57,c_80])).

tff(c_14,plain,(
    ! [A_11] : v1_zfmisc_1(k1_tarski(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_96,plain,(
    ! [B_29,A_30] :
      ( v1_subset_1(B_29,A_30)
      | ~ v1_zfmisc_1(B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | v1_zfmisc_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_2'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_96])).

tff(c_105,plain,
    ( v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_106,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_86,c_57,c_105])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v7_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_110,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_16])).

tff(c_113,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_113])).

%------------------------------------------------------------------------------
