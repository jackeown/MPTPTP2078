%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 313 expanded)
%              Number of leaves         :   39 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 (1006 expanded)
%              Number of equality atoms :   18 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_147,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1111,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k2_partfun1(A_252,B_253,C_254,D_255) = k7_relat_1(C_254,D_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1117,plain,(
    ! [D_255] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_255) = k7_relat_1('#skF_5',D_255)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1111])).

tff(c_1124,plain,(
    ! [D_255] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_255) = k7_relat_1('#skF_5',D_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1117])).

tff(c_1688,plain,(
    ! [B_337,A_338,D_339,C_340] :
      ( k1_xboole_0 = B_337
      | v1_funct_2(k2_partfun1(A_338,B_337,D_339,C_340),C_340,B_337)
      | ~ r1_tarski(C_340,A_338)
      | ~ m1_subset_1(D_339,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337)))
      | ~ v1_funct_2(D_339,A_338,B_337)
      | ~ v1_funct_1(D_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1710,plain,(
    ! [C_340] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5',C_340),C_340,'#skF_4')
      | ~ r1_tarski(C_340,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1688])).

tff(c_1737,plain,(
    ! [C_340] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(k7_relat_1('#skF_5',C_340),C_340,'#skF_4')
      | ~ r1_tarski(C_340,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1124,c_1710])).

tff(c_1738,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1743,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_2])).

tff(c_1745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1743])).

tff(c_1746,plain,(
    ! [C_340] :
      ( v1_funct_2(k7_relat_1('#skF_5',C_340),C_340,'#skF_4')
      | ~ r1_tarski(C_340,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_1011,plain,(
    ! [C_224,A_225,B_226] :
      ( v1_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1015,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1011])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1044,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( v1_funct_1(k2_partfun1(A_233,B_234,C_235,D_236))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1048,plain,(
    ! [D_236] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_236))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1044])).

tff(c_1054,plain,(
    ! [D_236] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_236)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1048])).

tff(c_1127,plain,(
    ! [D_236] : v1_funct_1(k7_relat_1('#skF_5',D_236)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1054])).

tff(c_1324,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( m1_subset_1(k2_partfun1(A_287,B_288,C_289,D_290),k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1350,plain,(
    ! [D_255] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_255),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_1324])).

tff(c_1365,plain,(
    ! [D_291] : m1_subset_1(k7_relat_1('#skF_5',D_291),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1350])).

tff(c_16,plain,(
    ! [D_20,B_18,C_19,A_17] :
      ( m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(B_18,C_19)))
      | ~ r1_tarski(k1_relat_1(D_20),B_18)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,C_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1629,plain,(
    ! [D_333,B_334] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_333),k1_zfmisc_1(k2_zfmisc_1(B_334,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5',D_333)),B_334) ) ),
    inference(resolution,[status(thm)],[c_1365,c_16])).

tff(c_22,plain,(
    ! [C_27,A_24,B_25] :
      ( v1_partfun1(C_27,A_24)
      | ~ v1_funct_2(C_27,A_24,B_25)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1637,plain,(
    ! [D_333,B_334] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_333),B_334)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_333),B_334,'#skF_4')
      | ~ v1_funct_1(k7_relat_1('#skF_5',D_333))
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5',D_333)),B_334) ) ),
    inference(resolution,[status(thm)],[c_1629,c_22])).

tff(c_1663,plain,(
    ! [D_333,B_334] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_333),B_334)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_333),B_334,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5',D_333)),B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_1637])).

tff(c_1748,plain,(
    ! [D_341,B_342] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_341),B_342)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_341),B_342,'#skF_4')
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5',D_341)),B_342) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1663])).

tff(c_1752,plain,(
    ! [A_8] :
      ( v1_partfun1(k7_relat_1('#skF_5',A_8),A_8)
      | ~ v1_funct_2(k7_relat_1('#skF_5',A_8),A_8,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_1748])).

tff(c_1763,plain,(
    ! [A_344] :
      ( v1_partfun1(k7_relat_1('#skF_5',A_344),A_344)
      | ~ v1_funct_2(k7_relat_1('#skF_5',A_344),A_344,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1752])).

tff(c_1773,plain,(
    ! [C_345] :
      ( v1_partfun1(k7_relat_1('#skF_5',C_345),C_345)
      | ~ r1_tarski(C_345,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1746,c_1763])).

tff(c_100,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_100])).

tff(c_130,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k7_relset_1(A_74,B_75,C_76,D_77) = k9_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    ! [D_77] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_77) = k9_relat_1('#skF_5',D_77) ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_52,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_134,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_52])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k2_partfun1(A_87,B_88,C_89,D_90) = k7_relat_1(C_89,D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_177,plain,(
    ! [D_90] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_90) = k7_relat_1('#skF_5',D_90)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_173])).

tff(c_181,plain,(
    ! [D_90] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_90) = k7_relat_1('#skF_5',D_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_177])).

tff(c_258,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( m1_subset_1(k2_partfun1(A_108,B_109,C_110,D_111),k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_281,plain,(
    ! [D_90] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_90),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_258])).

tff(c_294,plain,(
    ! [D_112] : m1_subset_1(k7_relat_1('#skF_5',D_112),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_281])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_311,plain,(
    ! [D_112] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_112))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_294,c_4])).

tff(c_332,plain,(
    ! [D_112] : v1_relat_1(k7_relat_1('#skF_5',D_112)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_311])).

tff(c_122,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( v1_funct_1(k2_partfun1(A_69,B_70,C_71,D_72))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_124,plain,(
    ! [D_72] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_72))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_127,plain,(
    ! [D_72] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_124])).

tff(c_189,plain,(
    ! [D_72] : v1_funct_1(k7_relat_1('#skF_5',D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_127])).

tff(c_44,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41),A_40)))
      | ~ r1_tarski(k2_relat_1(B_41),A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_182,plain,(
    ! [D_91,B_92,C_93,A_94] :
      ( m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(B_92,C_93)))
      | ~ r1_tarski(k1_relat_1(D_91),B_92)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_94,C_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_926,plain,(
    ! [B_219,B_220,A_221] :
      ( m1_subset_1(B_219,k1_zfmisc_1(k2_zfmisc_1(B_220,A_221)))
      | ~ r1_tarski(k1_relat_1(B_219),B_220)
      | ~ r1_tarski(k2_relat_1(B_219),A_221)
      | ~ v1_funct_1(B_219)
      | ~ v1_relat_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_88,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( v1_funct_1(k2_partfun1(A_56,B_57,C_58,D_59))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | ~ v1_funct_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_90,plain,(
    ! [D_59] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_59))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_93,plain,(
    ! [D_59] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_65,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_65])).

tff(c_97,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_99,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_190,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_99])).

tff(c_939,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_926,c_190])).

tff(c_963,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_189,c_939])).

tff(c_973,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_981,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_973])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_134,c_981])).

tff(c_985,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1004,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_985])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1004])).

tff(c_1009,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_1010,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_1075,plain,(
    ! [C_244,A_245,B_246] :
      ( v1_funct_2(C_244,A_245,B_246)
      | ~ v1_partfun1(C_244,A_245)
      | ~ v1_funct_1(C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1078,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1010,c_1075])).

tff(c_1084,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1078])).

tff(c_1085,plain,(
    ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1009,c_1084])).

tff(c_1125,plain,(
    ~ v1_partfun1(k7_relat_1('#skF_5','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1085])).

tff(c_1776,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1773,c_1125])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.90  
% 4.21/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.90  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.21/1.90  
% 4.21/1.90  %Foreground sorts:
% 4.21/1.90  
% 4.21/1.90  
% 4.21/1.90  %Background operators:
% 4.21/1.90  
% 4.21/1.90  
% 4.21/1.90  %Foreground operators:
% 4.21/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.21/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.21/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.21/1.90  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.21/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.21/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.21/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.21/1.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.21/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.21/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.21/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.21/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.21/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.21/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.21/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.90  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.21/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.21/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.21/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.21/1.90  
% 4.37/1.93  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 4.37/1.93  tff(f_95, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.37/1.93  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 4.37/1.93  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.37/1.93  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.37/1.93  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.37/1.93  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.37/1.93  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.37/1.93  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.37/1.93  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.37/1.93  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.37/1.93  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.37/1.93  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.37/1.93  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.37/1.93  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.37/1.93  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_1111, plain, (![A_252, B_253, C_254, D_255]: (k2_partfun1(A_252, B_253, C_254, D_255)=k7_relat_1(C_254, D_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~v1_funct_1(C_254))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.37/1.93  tff(c_1117, plain, (![D_255]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_255)=k7_relat_1('#skF_5', D_255) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1111])).
% 4.37/1.93  tff(c_1124, plain, (![D_255]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_255)=k7_relat_1('#skF_5', D_255))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1117])).
% 4.37/1.93  tff(c_1688, plain, (![B_337, A_338, D_339, C_340]: (k1_xboole_0=B_337 | v1_funct_2(k2_partfun1(A_338, B_337, D_339, C_340), C_340, B_337) | ~r1_tarski(C_340, A_338) | ~m1_subset_1(D_339, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))) | ~v1_funct_2(D_339, A_338, B_337) | ~v1_funct_1(D_339))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.37/1.93  tff(c_1710, plain, (![C_340]: (k1_xboole_0='#skF_4' | v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', C_340), C_340, '#skF_4') | ~r1_tarski(C_340, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1688])).
% 4.37/1.93  tff(c_1737, plain, (![C_340]: (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_5', C_340), C_340, '#skF_4') | ~r1_tarski(C_340, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1124, c_1710])).
% 4.37/1.93  tff(c_1738, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1737])).
% 4.37/1.93  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.37/1.93  tff(c_1743, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1738, c_2])).
% 4.37/1.93  tff(c_1745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1743])).
% 4.37/1.93  tff(c_1746, plain, (![C_340]: (v1_funct_2(k7_relat_1('#skF_5', C_340), C_340, '#skF_4') | ~r1_tarski(C_340, '#skF_1'))), inference(splitRight, [status(thm)], [c_1737])).
% 4.37/1.93  tff(c_1011, plain, (![C_224, A_225, B_226]: (v1_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.93  tff(c_1015, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1011])).
% 4.37/1.93  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.93  tff(c_1044, plain, (![A_233, B_234, C_235, D_236]: (v1_funct_1(k2_partfun1(A_233, B_234, C_235, D_236)) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(C_235))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.37/1.93  tff(c_1048, plain, (![D_236]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_236)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1044])).
% 4.37/1.93  tff(c_1054, plain, (![D_236]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_236)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1048])).
% 4.37/1.93  tff(c_1127, plain, (![D_236]: (v1_funct_1(k7_relat_1('#skF_5', D_236)))), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1054])).
% 4.37/1.93  tff(c_1324, plain, (![A_287, B_288, C_289, D_290]: (m1_subset_1(k2_partfun1(A_287, B_288, C_289, D_290), k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(C_289))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.37/1.93  tff(c_1350, plain, (![D_255]: (m1_subset_1(k7_relat_1('#skF_5', D_255), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1124, c_1324])).
% 4.37/1.93  tff(c_1365, plain, (![D_291]: (m1_subset_1(k7_relat_1('#skF_5', D_291), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1350])).
% 4.37/1.93  tff(c_16, plain, (![D_20, B_18, C_19, A_17]: (m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(B_18, C_19))) | ~r1_tarski(k1_relat_1(D_20), B_18) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, C_19))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.37/1.93  tff(c_1629, plain, (![D_333, B_334]: (m1_subset_1(k7_relat_1('#skF_5', D_333), k1_zfmisc_1(k2_zfmisc_1(B_334, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', D_333)), B_334))), inference(resolution, [status(thm)], [c_1365, c_16])).
% 4.37/1.93  tff(c_22, plain, (![C_27, A_24, B_25]: (v1_partfun1(C_27, A_24) | ~v1_funct_2(C_27, A_24, B_25) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/1.93  tff(c_1637, plain, (![D_333, B_334]: (v1_partfun1(k7_relat_1('#skF_5', D_333), B_334) | ~v1_funct_2(k7_relat_1('#skF_5', D_333), B_334, '#skF_4') | ~v1_funct_1(k7_relat_1('#skF_5', D_333)) | v1_xboole_0('#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', D_333)), B_334))), inference(resolution, [status(thm)], [c_1629, c_22])).
% 4.37/1.93  tff(c_1663, plain, (![D_333, B_334]: (v1_partfun1(k7_relat_1('#skF_5', D_333), B_334) | ~v1_funct_2(k7_relat_1('#skF_5', D_333), B_334, '#skF_4') | v1_xboole_0('#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', D_333)), B_334))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1637])).
% 4.37/1.93  tff(c_1748, plain, (![D_341, B_342]: (v1_partfun1(k7_relat_1('#skF_5', D_341), B_342) | ~v1_funct_2(k7_relat_1('#skF_5', D_341), B_342, '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', D_341)), B_342))), inference(negUnitSimplification, [status(thm)], [c_62, c_1663])).
% 4.37/1.93  tff(c_1752, plain, (![A_8]: (v1_partfun1(k7_relat_1('#skF_5', A_8), A_8) | ~v1_funct_2(k7_relat_1('#skF_5', A_8), A_8, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_1748])).
% 4.37/1.93  tff(c_1763, plain, (![A_344]: (v1_partfun1(k7_relat_1('#skF_5', A_344), A_344) | ~v1_funct_2(k7_relat_1('#skF_5', A_344), A_344, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1752])).
% 4.37/1.93  tff(c_1773, plain, (![C_345]: (v1_partfun1(k7_relat_1('#skF_5', C_345), C_345) | ~r1_tarski(C_345, '#skF_1'))), inference(resolution, [status(thm)], [c_1746, c_1763])).
% 4.37/1.93  tff(c_100, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.93  tff(c_104, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_100])).
% 4.37/1.93  tff(c_130, plain, (![A_74, B_75, C_76, D_77]: (k7_relset_1(A_74, B_75, C_76, D_77)=k9_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/1.93  tff(c_133, plain, (![D_77]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_77)=k9_relat_1('#skF_5', D_77))), inference(resolution, [status(thm)], [c_56, c_130])).
% 4.37/1.93  tff(c_52, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_134, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_52])).
% 4.37/1.93  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.37/1.93  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.37/1.93  tff(c_173, plain, (![A_87, B_88, C_89, D_90]: (k2_partfun1(A_87, B_88, C_89, D_90)=k7_relat_1(C_89, D_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.37/1.93  tff(c_177, plain, (![D_90]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_90)=k7_relat_1('#skF_5', D_90) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_173])).
% 4.37/1.93  tff(c_181, plain, (![D_90]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_90)=k7_relat_1('#skF_5', D_90))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_177])).
% 4.37/1.93  tff(c_258, plain, (![A_108, B_109, C_110, D_111]: (m1_subset_1(k2_partfun1(A_108, B_109, C_110, D_111), k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.37/1.93  tff(c_281, plain, (![D_90]: (m1_subset_1(k7_relat_1('#skF_5', D_90), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_258])).
% 4.37/1.93  tff(c_294, plain, (![D_112]: (m1_subset_1(k7_relat_1('#skF_5', D_112), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_281])).
% 4.37/1.93  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.93  tff(c_311, plain, (![D_112]: (v1_relat_1(k7_relat_1('#skF_5', D_112)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_294, c_4])).
% 4.37/1.93  tff(c_332, plain, (![D_112]: (v1_relat_1(k7_relat_1('#skF_5', D_112)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_311])).
% 4.37/1.93  tff(c_122, plain, (![A_69, B_70, C_71, D_72]: (v1_funct_1(k2_partfun1(A_69, B_70, C_71, D_72)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.37/1.93  tff(c_124, plain, (![D_72]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_72)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 4.37/1.93  tff(c_127, plain, (![D_72]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_124])).
% 4.37/1.93  tff(c_189, plain, (![D_72]: (v1_funct_1(k7_relat_1('#skF_5', D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_127])).
% 4.37/1.93  tff(c_44, plain, (![B_41, A_40]: (m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41), A_40))) | ~r1_tarski(k2_relat_1(B_41), A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.37/1.93  tff(c_182, plain, (![D_91, B_92, C_93, A_94]: (m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(B_92, C_93))) | ~r1_tarski(k1_relat_1(D_91), B_92) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_94, C_93))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.37/1.93  tff(c_926, plain, (![B_219, B_220, A_221]: (m1_subset_1(B_219, k1_zfmisc_1(k2_zfmisc_1(B_220, A_221))) | ~r1_tarski(k1_relat_1(B_219), B_220) | ~r1_tarski(k2_relat_1(B_219), A_221) | ~v1_funct_1(B_219) | ~v1_relat_1(B_219))), inference(resolution, [status(thm)], [c_44, c_182])).
% 4.37/1.93  tff(c_88, plain, (![A_56, B_57, C_58, D_59]: (v1_funct_1(k2_partfun1(A_56, B_57, C_58, D_59)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | ~v1_funct_1(C_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.37/1.93  tff(c_90, plain, (![D_59]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_59)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_88])).
% 4.37/1.93  tff(c_93, plain, (![D_59]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_59)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_90])).
% 4.37/1.93  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.93  tff(c_65, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.37/1.93  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_65])).
% 4.37/1.93  tff(c_97, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 4.37/1.93  tff(c_99, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_97])).
% 4.37/1.93  tff(c_190, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_99])).
% 4.37/1.93  tff(c_939, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~v1_funct_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_926, c_190])).
% 4.37/1.93  tff(c_963, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_189, c_939])).
% 4.37/1.93  tff(c_973, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_963])).
% 4.37/1.93  tff(c_981, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8, c_973])).
% 4.37/1.93  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_134, c_981])).
% 4.37/1.93  tff(c_985, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_963])).
% 4.37/1.93  tff(c_1004, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_985])).
% 4.37/1.93  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1004])).
% 4.37/1.93  tff(c_1009, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_97])).
% 4.37/1.93  tff(c_1010, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_97])).
% 4.37/1.93  tff(c_1075, plain, (![C_244, A_245, B_246]: (v1_funct_2(C_244, A_245, B_246) | ~v1_partfun1(C_244, A_245) | ~v1_funct_1(C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.37/1.93  tff(c_1078, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_1010, c_1075])).
% 4.37/1.93  tff(c_1084, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1078])).
% 4.37/1.93  tff(c_1085, plain, (~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1009, c_1084])).
% 4.37/1.93  tff(c_1125, plain, (~v1_partfun1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1085])).
% 4.37/1.93  tff(c_1776, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1773, c_1125])).
% 4.37/1.93  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1776])).
% 4.37/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.93  
% 4.37/1.93  Inference rules
% 4.37/1.93  ----------------------
% 4.37/1.93  #Ref     : 0
% 4.37/1.93  #Sup     : 335
% 4.37/1.93  #Fact    : 0
% 4.37/1.93  #Define  : 0
% 4.37/1.93  #Split   : 9
% 4.37/1.93  #Chain   : 0
% 4.37/1.93  #Close   : 0
% 4.37/1.93  
% 4.37/1.93  Ordering : KBO
% 4.37/1.93  
% 4.37/1.93  Simplification rules
% 4.37/1.93  ----------------------
% 4.37/1.93  #Subsume      : 29
% 4.37/1.93  #Demod        : 267
% 4.37/1.93  #Tautology    : 99
% 4.37/1.93  #SimpNegUnit  : 24
% 4.37/1.93  #BackRed      : 24
% 4.37/1.93  
% 4.37/1.93  #Partial instantiations: 0
% 4.37/1.93  #Strategies tried      : 1
% 4.37/1.93  
% 4.37/1.93  Timing (in seconds)
% 4.37/1.93  ----------------------
% 4.37/1.93  Preprocessing        : 0.41
% 4.37/1.93  Parsing              : 0.22
% 4.37/1.93  CNF conversion       : 0.02
% 4.37/1.93  Main loop            : 0.57
% 4.37/1.93  Inferencing          : 0.21
% 4.37/1.93  Reduction            : 0.19
% 4.37/1.93  Demodulation         : 0.14
% 4.37/1.93  BG Simplification    : 0.03
% 4.37/1.93  Subsumption          : 0.09
% 4.37/1.93  Abstraction          : 0.03
% 4.37/1.93  MUC search           : 0.00
% 4.37/1.93  Cooper               : 0.00
% 4.37/1.93  Total                : 1.02
% 4.37/1.93  Index Insertion      : 0.00
% 4.37/1.93  Index Deletion       : 0.00
% 4.37/1.93  Index Matching       : 0.00
% 4.37/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
