%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:39 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 348 expanded)
%              Number of leaves         :   36 ( 128 expanded)
%              Depth                    :   14
%              Number of atoms          :  232 (1070 expanded)
%              Number of equality atoms :   59 ( 154 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1023,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k7_relset_1(A_247,B_248,C_249,D_250) = k9_relat_1(C_249,D_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1029,plain,(
    ! [D_250] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_250) = k9_relat_1('#skF_5',D_250) ),
    inference(resolution,[status(thm)],[c_46,c_1023])).

tff(c_42,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1030,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_42])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1082,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k2_partfun1(A_264,B_265,C_266,D_267) = k7_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265)))
      | ~ v1_funct_1(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1088,plain,(
    ! [D_267] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_267) = k7_relat_1('#skF_5',D_267)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1082])).

tff(c_1095,plain,(
    ! [D_267] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_267) = k7_relat_1('#skF_5',D_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1088])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_117,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_relset_1(A_61,B_62,C_63,D_64) = k9_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [D_64] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_64) = k9_relat_1('#skF_5',D_64) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_121,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_42])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_173,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k2_partfun1(A_84,B_85,C_86,D_87) = k7_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_177,plain,(
    ! [D_87] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_87) = k7_relat_1('#skF_5',D_87)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_173])).

tff(c_181,plain,(
    ! [D_87] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_87) = k7_relat_1('#skF_5',D_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_177])).

tff(c_312,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( m1_subset_1(k2_partfun1(A_100,B_101,C_102,D_103),k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_345,plain,(
    ! [D_87] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_87),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_312])).

tff(c_360,plain,(
    ! [D_104] : m1_subset_1(k7_relat_1('#skF_5',D_104),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_345])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_378,plain,(
    ! [D_104] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_104))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_360,c_4])).

tff(c_391,plain,(
    ! [D_104] : v1_relat_1(k7_relat_1('#skF_5',D_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_378])).

tff(c_131,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( v1_funct_1(k2_partfun1(A_66,B_67,C_68,D_69))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_133,plain,(
    ! [D_69] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_69))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_131])).

tff(c_136,plain,(
    ! [D_69] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_133])).

tff(c_182,plain,(
    ! [D_69] : v1_funct_1(k7_relat_1('#skF_5',D_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_136])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_106,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_106])).

tff(c_204,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_204])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_110,c_210])).

tff(c_215,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_relat_1(k7_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_229,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_10])).

tff(c_246,plain,(
    ! [A_97] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_97)) = A_97
      | ~ r1_tarski(A_97,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_229])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_29),A_28)))
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_255,plain,(
    ! [A_97,A_28] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_97),k1_zfmisc_1(k2_zfmisc_1(A_97,A_28)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_97)),A_28)
      | ~ v1_funct_1(k7_relat_1('#skF_5',A_97))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_97))
      | ~ r1_tarski(A_97,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_34])).

tff(c_269,plain,(
    ! [A_97,A_28] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_97),k1_zfmisc_1(k2_zfmisc_1(A_97,A_28)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_97)),A_28)
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_97))
      | ~ r1_tarski(A_97,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_255])).

tff(c_864,plain,(
    ! [A_233,A_234] :
      ( m1_subset_1(k7_relat_1('#skF_5',A_233),k1_zfmisc_1(k2_zfmisc_1(A_233,A_234)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_233)),A_234)
      | ~ r1_tarski(A_233,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_269])).

tff(c_84,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( v1_funct_1(k2_partfun1(A_47,B_48,C_49,D_50))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,(
    ! [D_50] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_50))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_89,plain,(
    ! [D_50] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86])).

tff(c_40,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_61,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_61])).

tff(c_93,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_116,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_183,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_116])).

tff(c_874,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_864,c_183])).

tff(c_911,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_874])).

tff(c_929,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_911])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_121,c_929])).

tff(c_933,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_989,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_2])).

tff(c_991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_989])).

tff(c_993,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_999,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_993,c_4])).

tff(c_1003,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_999])).

tff(c_1115,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1003])).

tff(c_1008,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( v1_funct_1(k2_partfun1(A_239,B_240,C_241,D_242))
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ v1_funct_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1012,plain,(
    ! [D_242] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_242))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1008])).

tff(c_1018,plain,(
    ! [D_242] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_242)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1012])).

tff(c_1114,plain,(
    ! [D_242] : v1_funct_1(k7_relat_1('#skF_5',D_242)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1018])).

tff(c_1162,plain,(
    ! [B_274,A_275,C_276] :
      ( k1_xboole_0 = B_274
      | k1_relset_1(A_275,B_274,C_276) = A_275
      | ~ v1_funct_2(C_276,A_275,B_274)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1171,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1162])).

tff(c_1176,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_110,c_1171])).

tff(c_1177,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1191,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_10])).

tff(c_1209,plain,(
    ! [A_278] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_278)) = A_278
      | ~ r1_tarski(A_278,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1191])).

tff(c_992,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1000,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_993,c_12])).

tff(c_1096,plain,(
    ! [B_268,C_269,A_270] :
      ( k1_xboole_0 = B_268
      | v1_funct_2(C_269,A_270,B_268)
      | k1_relset_1(A_270,B_268,C_269) != A_270
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1102,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_993,c_1096])).

tff(c_1108,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1102])).

tff(c_1109,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_992,c_1108])).

tff(c_1160,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1109])).

tff(c_1161,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1160])).

tff(c_1215,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_1161])).

tff(c_1235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1215])).

tff(c_1236,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1244,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1236,c_2])).

tff(c_1246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1244])).

tff(c_1248,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( v1_funct_2(B_29,k1_relat_1(B_29),A_28)
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1284,plain,(
    ! [A_28] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_28)
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),A_28)
      | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_36])).

tff(c_1512,plain,(
    ! [A_300] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_300)
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),A_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1114,c_1284])).

tff(c_1515,plain,(
    ! [A_300] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_300)
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_300)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1512])).

tff(c_1518,plain,(
    ! [A_301] :
      ( v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2',A_301)
      | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1515])).

tff(c_1118,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_992])).

tff(c_1521,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1518,c_1118])).

tff(c_1525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_1521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.67  
% 3.60/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.68  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.60/1.68  
% 3.60/1.68  %Foreground sorts:
% 3.60/1.68  
% 3.60/1.68  
% 3.60/1.68  %Background operators:
% 3.60/1.68  
% 3.60/1.68  
% 3.60/1.68  %Foreground operators:
% 3.60/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.60/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.60/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.60/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.60/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.60/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.68  
% 3.90/1.70  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 3.90/1.70  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.90/1.70  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.70  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.70  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.90/1.70  tff(f_85, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.90/1.70  tff(f_79, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.90/1.70  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.70  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.90/1.70  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.90/1.70  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.90/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.90/1.70  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_1023, plain, (![A_247, B_248, C_249, D_250]: (k7_relset_1(A_247, B_248, C_249, D_250)=k9_relat_1(C_249, D_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.70  tff(c_1029, plain, (![D_250]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_250)=k9_relat_1('#skF_5', D_250))), inference(resolution, [status(thm)], [c_46, c_1023])).
% 3.90/1.70  tff(c_42, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_1030, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_42])).
% 3.90/1.70  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.70  tff(c_54, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.70  tff(c_57, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.90/1.70  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 3.90/1.70  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.70  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_1082, plain, (![A_264, B_265, C_266, D_267]: (k2_partfun1(A_264, B_265, C_266, D_267)=k7_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))) | ~v1_funct_1(C_266))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.70  tff(c_1088, plain, (![D_267]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_267)=k7_relat_1('#skF_5', D_267) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1082])).
% 3.90/1.70  tff(c_1095, plain, (![D_267]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_267)=k7_relat_1('#skF_5', D_267))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1088])).
% 3.90/1.70  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_117, plain, (![A_61, B_62, C_63, D_64]: (k7_relset_1(A_61, B_62, C_63, D_64)=k9_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.70  tff(c_120, plain, (![D_64]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_64)=k9_relat_1('#skF_5', D_64))), inference(resolution, [status(thm)], [c_46, c_117])).
% 3.90/1.70  tff(c_121, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_42])).
% 3.90/1.70  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_173, plain, (![A_84, B_85, C_86, D_87]: (k2_partfun1(A_84, B_85, C_86, D_87)=k7_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.70  tff(c_177, plain, (![D_87]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_87)=k7_relat_1('#skF_5', D_87) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_173])).
% 3.90/1.70  tff(c_181, plain, (![D_87]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_87)=k7_relat_1('#skF_5', D_87))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_177])).
% 3.90/1.70  tff(c_312, plain, (![A_100, B_101, C_102, D_103]: (m1_subset_1(k2_partfun1(A_100, B_101, C_102, D_103), k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(C_102))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.70  tff(c_345, plain, (![D_87]: (m1_subset_1(k7_relat_1('#skF_5', D_87), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_312])).
% 3.90/1.70  tff(c_360, plain, (![D_104]: (m1_subset_1(k7_relat_1('#skF_5', D_104), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_345])).
% 3.90/1.70  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.70  tff(c_378, plain, (![D_104]: (v1_relat_1(k7_relat_1('#skF_5', D_104)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_360, c_4])).
% 3.90/1.70  tff(c_391, plain, (![D_104]: (v1_relat_1(k7_relat_1('#skF_5', D_104)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_378])).
% 3.90/1.70  tff(c_131, plain, (![A_66, B_67, C_68, D_69]: (v1_funct_1(k2_partfun1(A_66, B_67, C_68, D_69)) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.70  tff(c_133, plain, (![D_69]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_69)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_131])).
% 3.90/1.70  tff(c_136, plain, (![D_69]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_69)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_133])).
% 3.90/1.70  tff(c_182, plain, (![D_69]: (v1_funct_1(k7_relat_1('#skF_5', D_69)))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_136])).
% 3.90/1.70  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_106, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.90/1.70  tff(c_110, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_106])).
% 3.90/1.70  tff(c_204, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.70  tff(c_210, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_204])).
% 3.90/1.70  tff(c_214, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_110, c_210])).
% 3.90/1.70  tff(c_215, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_214])).
% 3.90/1.70  tff(c_10, plain, (![B_9, A_8]: (k1_relat_1(k7_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.90/1.70  tff(c_229, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_5', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_10])).
% 3.90/1.70  tff(c_246, plain, (![A_97]: (k1_relat_1(k7_relat_1('#skF_5', A_97))=A_97 | ~r1_tarski(A_97, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_229])).
% 3.90/1.70  tff(c_34, plain, (![B_29, A_28]: (m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_29), A_28))) | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.90/1.70  tff(c_255, plain, (![A_97, A_28]: (m1_subset_1(k7_relat_1('#skF_5', A_97), k1_zfmisc_1(k2_zfmisc_1(A_97, A_28))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_97)), A_28) | ~v1_funct_1(k7_relat_1('#skF_5', A_97)) | ~v1_relat_1(k7_relat_1('#skF_5', A_97)) | ~r1_tarski(A_97, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_34])).
% 3.90/1.70  tff(c_269, plain, (![A_97, A_28]: (m1_subset_1(k7_relat_1('#skF_5', A_97), k1_zfmisc_1(k2_zfmisc_1(A_97, A_28))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_97)), A_28) | ~v1_relat_1(k7_relat_1('#skF_5', A_97)) | ~r1_tarski(A_97, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_255])).
% 3.90/1.70  tff(c_864, plain, (![A_233, A_234]: (m1_subset_1(k7_relat_1('#skF_5', A_233), k1_zfmisc_1(k2_zfmisc_1(A_233, A_234))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_233)), A_234) | ~r1_tarski(A_233, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_269])).
% 3.90/1.70  tff(c_84, plain, (![A_47, B_48, C_49, D_50]: (v1_funct_1(k2_partfun1(A_47, B_48, C_49, D_50)) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(C_49))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.70  tff(c_86, plain, (![D_50]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_50)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.90/1.70  tff(c_89, plain, (![D_50]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_50)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86])).
% 3.90/1.70  tff(c_40, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.90/1.70  tff(c_61, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.90/1.70  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_61])).
% 3.90/1.70  tff(c_93, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 3.90/1.70  tff(c_116, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_93])).
% 3.90/1.70  tff(c_183, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_116])).
% 3.90/1.70  tff(c_874, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_864, c_183])).
% 3.90/1.70  tff(c_911, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_874])).
% 3.90/1.70  tff(c_929, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8, c_911])).
% 3.90/1.70  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_121, c_929])).
% 3.90/1.70  tff(c_933, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_214])).
% 3.90/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.90/1.70  tff(c_989, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_933, c_2])).
% 3.90/1.70  tff(c_991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_989])).
% 3.90/1.70  tff(c_993, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_93])).
% 3.90/1.70  tff(c_999, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_993, c_4])).
% 3.90/1.70  tff(c_1003, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_999])).
% 3.90/1.70  tff(c_1115, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1003])).
% 3.90/1.70  tff(c_1008, plain, (![A_239, B_240, C_241, D_242]: (v1_funct_1(k2_partfun1(A_239, B_240, C_241, D_242)) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~v1_funct_1(C_241))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.70  tff(c_1012, plain, (![D_242]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_242)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1008])).
% 3.90/1.70  tff(c_1018, plain, (![D_242]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_242)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1012])).
% 3.90/1.70  tff(c_1114, plain, (![D_242]: (v1_funct_1(k7_relat_1('#skF_5', D_242)))), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1018])).
% 3.90/1.70  tff(c_1162, plain, (![B_274, A_275, C_276]: (k1_xboole_0=B_274 | k1_relset_1(A_275, B_274, C_276)=A_275 | ~v1_funct_2(C_276, A_275, B_274) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.70  tff(c_1171, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_1162])).
% 3.90/1.70  tff(c_1176, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_110, c_1171])).
% 3.90/1.70  tff(c_1177, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_1176])).
% 3.90/1.70  tff(c_1191, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_5', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1177, c_10])).
% 3.90/1.70  tff(c_1209, plain, (![A_278]: (k1_relat_1(k7_relat_1('#skF_5', A_278))=A_278 | ~r1_tarski(A_278, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1191])).
% 3.90/1.70  tff(c_992, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 3.90/1.70  tff(c_12, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.90/1.70  tff(c_1000, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_993, c_12])).
% 3.90/1.70  tff(c_1096, plain, (![B_268, C_269, A_270]: (k1_xboole_0=B_268 | v1_funct_2(C_269, A_270, B_268) | k1_relset_1(A_270, B_268, C_269)!=A_270 | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_268))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.70  tff(c_1102, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_993, c_1096])).
% 3.90/1.70  tff(c_1108, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1102])).
% 3.90/1.70  tff(c_1109, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_992, c_1108])).
% 3.90/1.70  tff(c_1160, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1109])).
% 3.90/1.70  tff(c_1161, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1160])).
% 3.90/1.70  tff(c_1215, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1209, c_1161])).
% 3.90/1.70  tff(c_1235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1215])).
% 3.90/1.70  tff(c_1236, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1176])).
% 3.90/1.70  tff(c_1244, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1236, c_2])).
% 3.90/1.70  tff(c_1246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1244])).
% 3.90/1.70  tff(c_1248, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_1160])).
% 3.90/1.70  tff(c_36, plain, (![B_29, A_28]: (v1_funct_2(B_29, k1_relat_1(B_29), A_28) | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.90/1.70  tff(c_1284, plain, (![A_28]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_28) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), A_28) | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1248, c_36])).
% 3.90/1.70  tff(c_1512, plain, (![A_300]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_300) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), A_300))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1114, c_1284])).
% 3.90/1.70  tff(c_1515, plain, (![A_300]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_300) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_300) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1512])).
% 3.90/1.70  tff(c_1518, plain, (![A_301]: (v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', A_301) | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_301))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1515])).
% 3.90/1.70  tff(c_1118, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_992])).
% 3.90/1.70  tff(c_1521, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1518, c_1118])).
% 3.90/1.70  tff(c_1525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1030, c_1521])).
% 3.90/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.70  
% 3.90/1.70  Inference rules
% 3.90/1.70  ----------------------
% 3.90/1.70  #Ref     : 0
% 3.90/1.70  #Sup     : 295
% 3.90/1.70  #Fact    : 0
% 3.90/1.70  #Define  : 0
% 3.90/1.70  #Split   : 9
% 3.90/1.70  #Chain   : 0
% 3.90/1.70  #Close   : 0
% 3.90/1.70  
% 3.90/1.70  Ordering : KBO
% 3.90/1.70  
% 3.90/1.70  Simplification rules
% 3.90/1.70  ----------------------
% 3.90/1.70  #Subsume      : 21
% 3.90/1.70  #Demod        : 294
% 3.90/1.70  #Tautology    : 98
% 3.90/1.70  #SimpNegUnit  : 12
% 3.90/1.70  #BackRed      : 48
% 3.90/1.70  
% 3.90/1.70  #Partial instantiations: 0
% 3.90/1.70  #Strategies tried      : 1
% 3.90/1.70  
% 3.90/1.70  Timing (in seconds)
% 3.90/1.70  ----------------------
% 3.90/1.70  Preprocessing        : 0.35
% 3.90/1.70  Parsing              : 0.19
% 3.90/1.70  CNF conversion       : 0.02
% 3.90/1.70  Main loop            : 0.51
% 3.90/1.70  Inferencing          : 0.19
% 3.90/1.70  Reduction            : 0.17
% 3.90/1.70  Demodulation         : 0.12
% 3.90/1.70  BG Simplification    : 0.03
% 3.90/1.70  Subsumption          : 0.07
% 3.90/1.70  Abstraction          : 0.03
% 3.90/1.70  MUC search           : 0.00
% 3.90/1.70  Cooper               : 0.00
% 3.90/1.70  Total                : 0.90
% 3.90/1.70  Index Insertion      : 0.00
% 3.90/1.70  Index Deletion       : 0.00
% 3.90/1.70  Index Matching       : 0.00
% 3.90/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
