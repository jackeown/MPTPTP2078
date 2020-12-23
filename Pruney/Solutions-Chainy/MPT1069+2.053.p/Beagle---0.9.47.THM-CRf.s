%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:52 EST 2020

% Result     : Theorem 12.40s
% Output     : CNFRefutation 12.40s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 339 expanded)
%              Number of leaves         :   46 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  263 (1196 expanded)
%              Number of equality atoms :   56 ( 232 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_42,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_161,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_239,plain,(
    ! [A_101,A_102,B_103] :
      ( r2_hidden(A_101,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102))
      | v1_xboole_0(B_103)
      | ~ m1_subset_1(A_101,B_103) ) ),
    inference(resolution,[status(thm)],[c_8,c_161])).

tff(c_15355,plain,(
    ! [A_2633,B_2634,A_2635] :
      ( r2_hidden(A_2633,B_2634)
      | v1_xboole_0(A_2635)
      | ~ m1_subset_1(A_2633,A_2635)
      | ~ r1_tarski(A_2635,B_2634) ) ),
    inference(resolution,[status(thm)],[c_12,c_239])).

tff(c_15367,plain,(
    ! [B_2634] :
      ( r2_hidden('#skF_6',B_2634)
      | v1_xboole_0('#skF_2')
      | ~ r1_tarski('#skF_2',B_2634) ) ),
    inference(resolution,[status(thm)],[c_42,c_15355])).

tff(c_15368,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15367])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_15371,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_15368,c_4])).

tff(c_15375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_15371])).

tff(c_15377,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_15367])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_166,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_178,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_166])).

tff(c_15386,plain,(
    ! [D_2637,C_2638,A_2639,B_2640] :
      ( r2_hidden(k1_funct_1(D_2637,C_2638),k2_relset_1(A_2639,B_2640,D_2637))
      | k1_xboole_0 = B_2640
      | ~ r2_hidden(C_2638,A_2639)
      | ~ m1_subset_1(D_2637,k1_zfmisc_1(k2_zfmisc_1(A_2639,B_2640)))
      | ~ v1_funct_2(D_2637,A_2639,B_2640)
      | ~ v1_funct_1(D_2637) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_15394,plain,(
    ! [C_2638] :
      ( r2_hidden(k1_funct_1('#skF_4',C_2638),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_2638,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_15386])).

tff(c_15399,plain,(
    ! [C_2638] :
      ( r2_hidden(k1_funct_1('#skF_4',C_2638),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_2638,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_15394])).

tff(c_15416,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15399])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_15419,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15416,c_2])).

tff(c_15422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_15419])).

tff(c_15424,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15399])).

tff(c_24566,plain,(
    ! [C_4094,E_4091,B_4095,A_4092,D_4093] :
      ( k1_funct_1(k5_relat_1(D_4093,E_4091),C_4094) = k1_funct_1(E_4091,k1_funct_1(D_4093,C_4094))
      | k1_xboole_0 = B_4095
      | ~ r2_hidden(C_4094,A_4092)
      | ~ v1_funct_1(E_4091)
      | ~ v1_relat_1(E_4091)
      | ~ m1_subset_1(D_4093,k1_zfmisc_1(k2_zfmisc_1(A_4092,B_4095)))
      | ~ v1_funct_2(D_4093,A_4092,B_4095)
      | ~ v1_funct_1(D_4093) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_27875,plain,(
    ! [B_4691,A_4694,D_4695,E_4692,B_4693] :
      ( k1_funct_1(k5_relat_1(D_4695,E_4692),A_4694) = k1_funct_1(E_4692,k1_funct_1(D_4695,A_4694))
      | k1_xboole_0 = B_4691
      | ~ v1_funct_1(E_4692)
      | ~ v1_relat_1(E_4692)
      | ~ m1_subset_1(D_4695,k1_zfmisc_1(k2_zfmisc_1(B_4693,B_4691)))
      | ~ v1_funct_2(D_4695,B_4693,B_4691)
      | ~ v1_funct_1(D_4695)
      | v1_xboole_0(B_4693)
      | ~ m1_subset_1(A_4694,B_4693) ) ),
    inference(resolution,[status(thm)],[c_8,c_24566])).

tff(c_27880,plain,(
    ! [E_4692,A_4694] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_4692),A_4694) = k1_funct_1(E_4692,k1_funct_1('#skF_4',A_4694))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_4692)
      | ~ v1_relat_1(E_4692)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4694,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_27875])).

tff(c_27886,plain,(
    ! [E_4692,A_4694] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_4692),A_4694) = k1_funct_1(E_4692,k1_funct_1('#skF_4',A_4694))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_4692)
      | ~ v1_relat_1(E_4692)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_4694,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27880])).

tff(c_27887,plain,(
    ! [E_4692,A_4694] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_4692),A_4694) = k1_funct_1(E_4692,k1_funct_1('#skF_4',A_4694))
      | ~ v1_funct_1(E_4692)
      | ~ v1_relat_1(E_4692)
      | ~ m1_subset_1(A_4694,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_15377,c_15424,c_27886])).

tff(c_185,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_198,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_185])).

tff(c_40,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_180,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_40])).

tff(c_212,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_180])).

tff(c_15425,plain,(
    ! [D_2646,A_2645,E_2648,F_2647,C_2650,B_2649] :
      ( k1_partfun1(A_2645,B_2649,C_2650,D_2646,E_2648,F_2647) = k5_relat_1(E_2648,F_2647)
      | ~ m1_subset_1(F_2647,k1_zfmisc_1(k2_zfmisc_1(C_2650,D_2646)))
      | ~ v1_funct_1(F_2647)
      | ~ m1_subset_1(E_2648,k1_zfmisc_1(k2_zfmisc_1(A_2645,B_2649)))
      | ~ v1_funct_1(E_2648) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_15432,plain,(
    ! [A_2645,B_2649,E_2648] :
      ( k1_partfun1(A_2645,B_2649,'#skF_3','#skF_1',E_2648,'#skF_5') = k5_relat_1(E_2648,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_2648,k1_zfmisc_1(k2_zfmisc_1(A_2645,B_2649)))
      | ~ v1_funct_1(E_2648) ) ),
    inference(resolution,[status(thm)],[c_44,c_15425])).

tff(c_27256,plain,(
    ! [A_4567,B_4568,E_4569] :
      ( k1_partfun1(A_4567,B_4568,'#skF_3','#skF_1',E_4569,'#skF_5') = k5_relat_1(E_4569,'#skF_5')
      | ~ m1_subset_1(E_4569,k1_zfmisc_1(k2_zfmisc_1(A_4567,B_4568)))
      | ~ v1_funct_1(E_4569) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_15432])).

tff(c_27263,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_27256])).

tff(c_27270,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27263])).

tff(c_27204,plain,(
    ! [B_4555,C_4554,E_4557,D_4558,A_4556] :
      ( k1_partfun1(A_4556,B_4555,B_4555,C_4554,D_4558,E_4557) = k8_funct_2(A_4556,B_4555,C_4554,D_4558,E_4557)
      | k1_xboole_0 = B_4555
      | ~ r1_tarski(k2_relset_1(A_4556,B_4555,D_4558),k1_relset_1(B_4555,C_4554,E_4557))
      | ~ m1_subset_1(E_4557,k1_zfmisc_1(k2_zfmisc_1(B_4555,C_4554)))
      | ~ v1_funct_1(E_4557)
      | ~ m1_subset_1(D_4558,k1_zfmisc_1(k2_zfmisc_1(A_4556,B_4555)))
      | ~ v1_funct_2(D_4558,A_4556,B_4555)
      | ~ v1_funct_1(D_4558) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27216,plain,(
    ! [C_4554,E_4557] :
      ( k1_partfun1('#skF_2','#skF_3','#skF_3',C_4554,'#skF_4',E_4557) = k8_funct_2('#skF_2','#skF_3',C_4554,'#skF_4',E_4557)
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',C_4554,E_4557))
      | ~ m1_subset_1(E_4557,k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_4554)))
      | ~ v1_funct_1(E_4557)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_27204])).

tff(c_27226,plain,(
    ! [C_4554,E_4557] :
      ( k1_partfun1('#skF_2','#skF_3','#skF_3',C_4554,'#skF_4',E_4557) = k8_funct_2('#skF_2','#skF_3',C_4554,'#skF_4',E_4557)
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',C_4554,E_4557))
      | ~ m1_subset_1(E_4557,k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_4554)))
      | ~ v1_funct_1(E_4557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_27216])).

tff(c_27916,plain,(
    ! [C_4704,E_4705] :
      ( k1_partfun1('#skF_2','#skF_3','#skF_3',C_4704,'#skF_4',E_4705) = k8_funct_2('#skF_2','#skF_3',C_4704,'#skF_4',E_4705)
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',C_4704,E_4705))
      | ~ m1_subset_1(E_4705,k1_zfmisc_1(k2_zfmisc_1('#skF_3',C_4704)))
      | ~ v1_funct_1(E_4705) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15424,c_27226])).

tff(c_27919,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_27916])).

tff(c_27921,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_212,c_27270,c_27919])).

tff(c_111,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_111])).

tff(c_15440,plain,(
    ! [C_2651] :
      ( r2_hidden(k1_funct_1('#skF_4',C_2651),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_2651,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_15399])).

tff(c_6,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24587,plain,(
    ! [C_4099,A_4100] :
      ( r2_hidden(k1_funct_1('#skF_4',C_4099),A_4100)
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_4100))
      | ~ r2_hidden(C_4099,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_15440,c_6])).

tff(c_27192,plain,(
    ! [C_4549,B_4550] :
      ( r2_hidden(k1_funct_1('#skF_4',C_4549),B_4550)
      | ~ r2_hidden(C_4549,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_4550) ) ),
    inference(resolution,[status(thm)],[c_12,c_24587])).

tff(c_28,plain,(
    ! [A_30,B_31,C_33] :
      ( k7_partfun1(A_30,B_31,C_33) = k1_funct_1(B_31,C_33)
      | ~ r2_hidden(C_33,k1_relat_1(B_31))
      | ~ v1_funct_1(B_31)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_27830,plain,(
    ! [A_4686,B_4687,C_4688] :
      ( k7_partfun1(A_4686,B_4687,k1_funct_1('#skF_4',C_4688)) = k1_funct_1(B_4687,k1_funct_1('#skF_4',C_4688))
      | ~ v1_funct_1(B_4687)
      | ~ v5_relat_1(B_4687,A_4686)
      | ~ v1_relat_1(B_4687)
      | ~ r2_hidden(C_4688,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(B_4687)) ) ),
    inference(resolution,[status(thm)],[c_27192,c_28])).

tff(c_27834,plain,(
    ! [A_4686,C_4688] :
      ( k7_partfun1(A_4686,'#skF_5',k1_funct_1('#skF_4',C_4688)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_4688))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_4686)
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(C_4688,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_212,c_27830])).

tff(c_27840,plain,(
    ! [A_4689,C_4690] :
      ( k7_partfun1(A_4689,'#skF_5',k1_funct_1('#skF_4',C_4690)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_4690))
      | ~ v5_relat_1('#skF_5',A_4689)
      | ~ r2_hidden(C_4690,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_46,c_27834])).

tff(c_36,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_27846,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27840,c_36])).

tff(c_27852,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_27846])).

tff(c_27854,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_27852])).

tff(c_27860,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_27854])).

tff(c_27864,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_27860])).

tff(c_27866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15377,c_27864])).

tff(c_27867,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_27852])).

tff(c_27922,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27921,c_27867])).

tff(c_27930,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27887,c_27922])).

tff(c_27934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_92,c_46,c_27930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.40/5.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.92  
% 12.40/5.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.40/5.92  
% 12.40/5.92  %Foreground sorts:
% 12.40/5.92  
% 12.40/5.92  
% 12.40/5.92  %Background operators:
% 12.40/5.92  
% 12.40/5.92  
% 12.40/5.92  %Foreground operators:
% 12.40/5.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.40/5.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.40/5.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.40/5.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.40/5.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.40/5.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.40/5.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.40/5.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.40/5.92  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 12.40/5.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.40/5.92  tff('#skF_5', type, '#skF_5': $i).
% 12.40/5.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.40/5.92  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 12.40/5.92  tff('#skF_6', type, '#skF_6': $i).
% 12.40/5.92  tff('#skF_2', type, '#skF_2': $i).
% 12.40/5.92  tff('#skF_3', type, '#skF_3': $i).
% 12.40/5.92  tff('#skF_1', type, '#skF_1': $i).
% 12.40/5.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.40/5.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.40/5.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.40/5.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.40/5.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.40/5.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.40/5.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.40/5.92  tff('#skF_4', type, '#skF_4': $i).
% 12.40/5.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.40/5.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.40/5.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.40/5.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.40/5.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.40/5.92  
% 12.40/5.94  tff(f_162, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 12.40/5.94  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.40/5.94  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.40/5.94  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.40/5.94  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 12.40/5.94  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 12.40/5.94  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.40/5.94  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.40/5.94  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 12.40/5.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.40/5.94  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 12.40/5.94  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.40/5.94  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.40/5.94  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 12.40/5.94  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.40/5.94  tff(f_98, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 12.40/5.94  tff(c_42, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.40/5.94  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_76, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.40/5.94  tff(c_85, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_76])).
% 12.40/5.94  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 12.40/5.94  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.40/5.94  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.40/5.94  tff(c_161, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.40/5.94  tff(c_239, plain, (![A_101, A_102, B_103]: (r2_hidden(A_101, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)) | v1_xboole_0(B_103) | ~m1_subset_1(A_101, B_103))), inference(resolution, [status(thm)], [c_8, c_161])).
% 12.40/5.94  tff(c_15355, plain, (![A_2633, B_2634, A_2635]: (r2_hidden(A_2633, B_2634) | v1_xboole_0(A_2635) | ~m1_subset_1(A_2633, A_2635) | ~r1_tarski(A_2635, B_2634))), inference(resolution, [status(thm)], [c_12, c_239])).
% 12.40/5.94  tff(c_15367, plain, (![B_2634]: (r2_hidden('#skF_6', B_2634) | v1_xboole_0('#skF_2') | ~r1_tarski('#skF_2', B_2634))), inference(resolution, [status(thm)], [c_42, c_15355])).
% 12.40/5.94  tff(c_15368, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_15367])).
% 12.40/5.94  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.40/5.94  tff(c_15371, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_15368, c_4])).
% 12.40/5.94  tff(c_15375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_15371])).
% 12.40/5.94  tff(c_15377, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_15367])).
% 12.40/5.94  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_166, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.40/5.94  tff(c_178, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_166])).
% 12.40/5.94  tff(c_15386, plain, (![D_2637, C_2638, A_2639, B_2640]: (r2_hidden(k1_funct_1(D_2637, C_2638), k2_relset_1(A_2639, B_2640, D_2637)) | k1_xboole_0=B_2640 | ~r2_hidden(C_2638, A_2639) | ~m1_subset_1(D_2637, k1_zfmisc_1(k2_zfmisc_1(A_2639, B_2640))) | ~v1_funct_2(D_2637, A_2639, B_2640) | ~v1_funct_1(D_2637))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.40/5.94  tff(c_15394, plain, (![C_2638]: (r2_hidden(k1_funct_1('#skF_4', C_2638), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_2638, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_15386])).
% 12.40/5.94  tff(c_15399, plain, (![C_2638]: (r2_hidden(k1_funct_1('#skF_4', C_2638), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(C_2638, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_15394])).
% 12.40/5.94  tff(c_15416, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_15399])).
% 12.40/5.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.40/5.94  tff(c_15419, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15416, c_2])).
% 12.40/5.94  tff(c_15422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_15419])).
% 12.40/5.94  tff(c_15424, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_15399])).
% 12.40/5.94  tff(c_24566, plain, (![C_4094, E_4091, B_4095, A_4092, D_4093]: (k1_funct_1(k5_relat_1(D_4093, E_4091), C_4094)=k1_funct_1(E_4091, k1_funct_1(D_4093, C_4094)) | k1_xboole_0=B_4095 | ~r2_hidden(C_4094, A_4092) | ~v1_funct_1(E_4091) | ~v1_relat_1(E_4091) | ~m1_subset_1(D_4093, k1_zfmisc_1(k2_zfmisc_1(A_4092, B_4095))) | ~v1_funct_2(D_4093, A_4092, B_4095) | ~v1_funct_1(D_4093))), inference(cnfTransformation, [status(thm)], [f_125])).
% 12.40/5.94  tff(c_27875, plain, (![B_4691, A_4694, D_4695, E_4692, B_4693]: (k1_funct_1(k5_relat_1(D_4695, E_4692), A_4694)=k1_funct_1(E_4692, k1_funct_1(D_4695, A_4694)) | k1_xboole_0=B_4691 | ~v1_funct_1(E_4692) | ~v1_relat_1(E_4692) | ~m1_subset_1(D_4695, k1_zfmisc_1(k2_zfmisc_1(B_4693, B_4691))) | ~v1_funct_2(D_4695, B_4693, B_4691) | ~v1_funct_1(D_4695) | v1_xboole_0(B_4693) | ~m1_subset_1(A_4694, B_4693))), inference(resolution, [status(thm)], [c_8, c_24566])).
% 12.40/5.94  tff(c_27880, plain, (![E_4692, A_4694]: (k1_funct_1(k5_relat_1('#skF_4', E_4692), A_4694)=k1_funct_1(E_4692, k1_funct_1('#skF_4', A_4694)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_4692) | ~v1_relat_1(E_4692) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4694, '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_27875])).
% 12.40/5.94  tff(c_27886, plain, (![E_4692, A_4694]: (k1_funct_1(k5_relat_1('#skF_4', E_4692), A_4694)=k1_funct_1(E_4692, k1_funct_1('#skF_4', A_4694)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_4692) | ~v1_relat_1(E_4692) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_4694, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_27880])).
% 12.40/5.94  tff(c_27887, plain, (![E_4692, A_4694]: (k1_funct_1(k5_relat_1('#skF_4', E_4692), A_4694)=k1_funct_1(E_4692, k1_funct_1('#skF_4', A_4694)) | ~v1_funct_1(E_4692) | ~v1_relat_1(E_4692) | ~m1_subset_1(A_4694, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_15377, c_15424, c_27886])).
% 12.40/5.94  tff(c_185, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.40/5.94  tff(c_198, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_185])).
% 12.40/5.94  tff(c_40, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_180, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_40])).
% 12.40/5.94  tff(c_212, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_180])).
% 12.40/5.94  tff(c_15425, plain, (![D_2646, A_2645, E_2648, F_2647, C_2650, B_2649]: (k1_partfun1(A_2645, B_2649, C_2650, D_2646, E_2648, F_2647)=k5_relat_1(E_2648, F_2647) | ~m1_subset_1(F_2647, k1_zfmisc_1(k2_zfmisc_1(C_2650, D_2646))) | ~v1_funct_1(F_2647) | ~m1_subset_1(E_2648, k1_zfmisc_1(k2_zfmisc_1(A_2645, B_2649))) | ~v1_funct_1(E_2648))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.40/5.94  tff(c_15432, plain, (![A_2645, B_2649, E_2648]: (k1_partfun1(A_2645, B_2649, '#skF_3', '#skF_1', E_2648, '#skF_5')=k5_relat_1(E_2648, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_2648, k1_zfmisc_1(k2_zfmisc_1(A_2645, B_2649))) | ~v1_funct_1(E_2648))), inference(resolution, [status(thm)], [c_44, c_15425])).
% 12.40/5.94  tff(c_27256, plain, (![A_4567, B_4568, E_4569]: (k1_partfun1(A_4567, B_4568, '#skF_3', '#skF_1', E_4569, '#skF_5')=k5_relat_1(E_4569, '#skF_5') | ~m1_subset_1(E_4569, k1_zfmisc_1(k2_zfmisc_1(A_4567, B_4568))) | ~v1_funct_1(E_4569))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_15432])).
% 12.40/5.94  tff(c_27263, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_27256])).
% 12.40/5.94  tff(c_27270, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_27263])).
% 12.40/5.94  tff(c_27204, plain, (![B_4555, C_4554, E_4557, D_4558, A_4556]: (k1_partfun1(A_4556, B_4555, B_4555, C_4554, D_4558, E_4557)=k8_funct_2(A_4556, B_4555, C_4554, D_4558, E_4557) | k1_xboole_0=B_4555 | ~r1_tarski(k2_relset_1(A_4556, B_4555, D_4558), k1_relset_1(B_4555, C_4554, E_4557)) | ~m1_subset_1(E_4557, k1_zfmisc_1(k2_zfmisc_1(B_4555, C_4554))) | ~v1_funct_1(E_4557) | ~m1_subset_1(D_4558, k1_zfmisc_1(k2_zfmisc_1(A_4556, B_4555))) | ~v1_funct_2(D_4558, A_4556, B_4555) | ~v1_funct_1(D_4558))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.40/5.94  tff(c_27216, plain, (![C_4554, E_4557]: (k1_partfun1('#skF_2', '#skF_3', '#skF_3', C_4554, '#skF_4', E_4557)=k8_funct_2('#skF_2', '#skF_3', C_4554, '#skF_4', E_4557) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', C_4554, E_4557)) | ~m1_subset_1(E_4557, k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_4554))) | ~v1_funct_1(E_4557) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_27204])).
% 12.40/5.94  tff(c_27226, plain, (![C_4554, E_4557]: (k1_partfun1('#skF_2', '#skF_3', '#skF_3', C_4554, '#skF_4', E_4557)=k8_funct_2('#skF_2', '#skF_3', C_4554, '#skF_4', E_4557) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', C_4554, E_4557)) | ~m1_subset_1(E_4557, k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_4554))) | ~v1_funct_1(E_4557))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_27216])).
% 12.40/5.94  tff(c_27916, plain, (![C_4704, E_4705]: (k1_partfun1('#skF_2', '#skF_3', '#skF_3', C_4704, '#skF_4', E_4705)=k8_funct_2('#skF_2', '#skF_3', C_4704, '#skF_4', E_4705) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', C_4704, E_4705)) | ~m1_subset_1(E_4705, k1_zfmisc_1(k2_zfmisc_1('#skF_3', C_4704))) | ~v1_funct_1(E_4705))), inference(negUnitSimplification, [status(thm)], [c_15424, c_27226])).
% 12.40/5.94  tff(c_27919, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_198, c_27916])).
% 12.40/5.94  tff(c_27921, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_212, c_27270, c_27919])).
% 12.40/5.94  tff(c_111, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.40/5.94  tff(c_124, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_111])).
% 12.40/5.94  tff(c_15440, plain, (![C_2651]: (r2_hidden(k1_funct_1('#skF_4', C_2651), k2_relat_1('#skF_4')) | ~r2_hidden(C_2651, '#skF_2'))), inference(splitRight, [status(thm)], [c_15399])).
% 12.40/5.94  tff(c_6, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.40/5.94  tff(c_24587, plain, (![C_4099, A_4100]: (r2_hidden(k1_funct_1('#skF_4', C_4099), A_4100) | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_4100)) | ~r2_hidden(C_4099, '#skF_2'))), inference(resolution, [status(thm)], [c_15440, c_6])).
% 12.40/5.94  tff(c_27192, plain, (![C_4549, B_4550]: (r2_hidden(k1_funct_1('#skF_4', C_4549), B_4550) | ~r2_hidden(C_4549, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), B_4550))), inference(resolution, [status(thm)], [c_12, c_24587])).
% 12.40/5.94  tff(c_28, plain, (![A_30, B_31, C_33]: (k7_partfun1(A_30, B_31, C_33)=k1_funct_1(B_31, C_33) | ~r2_hidden(C_33, k1_relat_1(B_31)) | ~v1_funct_1(B_31) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.40/5.94  tff(c_27830, plain, (![A_4686, B_4687, C_4688]: (k7_partfun1(A_4686, B_4687, k1_funct_1('#skF_4', C_4688))=k1_funct_1(B_4687, k1_funct_1('#skF_4', C_4688)) | ~v1_funct_1(B_4687) | ~v5_relat_1(B_4687, A_4686) | ~v1_relat_1(B_4687) | ~r2_hidden(C_4688, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(B_4687)))), inference(resolution, [status(thm)], [c_27192, c_28])).
% 12.40/5.94  tff(c_27834, plain, (![A_4686, C_4688]: (k7_partfun1(A_4686, '#skF_5', k1_funct_1('#skF_4', C_4688))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_4688)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_4686) | ~v1_relat_1('#skF_5') | ~r2_hidden(C_4688, '#skF_2'))), inference(resolution, [status(thm)], [c_212, c_27830])).
% 12.40/5.94  tff(c_27840, plain, (![A_4689, C_4690]: (k7_partfun1(A_4689, '#skF_5', k1_funct_1('#skF_4', C_4690))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', C_4690)) | ~v5_relat_1('#skF_5', A_4689) | ~r2_hidden(C_4690, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_46, c_27834])).
% 12.40/5.94  tff(c_36, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 12.40/5.94  tff(c_27846, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~r2_hidden('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27840, c_36])).
% 12.40/5.94  tff(c_27852, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_27846])).
% 12.40/5.94  tff(c_27854, plain, (~r2_hidden('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_27852])).
% 12.40/5.94  tff(c_27860, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_27854])).
% 12.40/5.94  tff(c_27864, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_27860])).
% 12.40/5.94  tff(c_27866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15377, c_27864])).
% 12.40/5.94  tff(c_27867, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_27852])).
% 12.40/5.94  tff(c_27922, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27921, c_27867])).
% 12.40/5.94  tff(c_27930, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27887, c_27922])).
% 12.40/5.94  tff(c_27934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_92, c_46, c_27930])).
% 12.40/5.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.40/5.94  
% 12.40/5.94  Inference rules
% 12.40/5.94  ----------------------
% 12.40/5.94  #Ref     : 0
% 12.40/5.94  #Sup     : 6175
% 12.40/5.94  #Fact    : 0
% 12.40/5.94  #Define  : 0
% 12.40/5.94  #Split   : 352
% 12.40/5.94  #Chain   : 0
% 12.40/5.94  #Close   : 0
% 12.40/5.94  
% 12.40/5.94  Ordering : KBO
% 12.40/5.94  
% 12.40/5.94  Simplification rules
% 12.40/5.94  ----------------------
% 12.40/5.94  #Subsume      : 1691
% 12.40/5.94  #Demod        : 5412
% 12.40/5.94  #Tautology    : 1843
% 12.40/5.94  #SimpNegUnit  : 428
% 12.40/5.94  #BackRed      : 722
% 12.40/5.94  
% 12.40/5.94  #Partial instantiations: 0
% 12.40/5.94  #Strategies tried      : 1
% 12.40/5.94  
% 12.40/5.94  Timing (in seconds)
% 12.40/5.94  ----------------------
% 12.40/5.95  Preprocessing        : 0.34
% 12.40/5.95  Parsing              : 0.18
% 12.40/5.95  CNF conversion       : 0.02
% 12.40/5.95  Main loop            : 4.84
% 12.40/5.95  Inferencing          : 1.48
% 12.40/5.95  Reduction            : 1.75
% 12.40/5.95  Demodulation         : 1.16
% 12.40/5.95  BG Simplification    : 0.13
% 12.40/5.95  Subsumption          : 1.17
% 12.40/5.95  Abstraction          : 0.19
% 12.40/5.95  MUC search           : 0.00
% 12.40/5.95  Cooper               : 0.00
% 12.40/5.95  Total                : 5.22
% 12.40/5.95  Index Insertion      : 0.00
% 12.40/5.95  Index Deletion       : 0.00
% 12.40/5.95  Index Matching       : 0.00
% 12.40/5.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
