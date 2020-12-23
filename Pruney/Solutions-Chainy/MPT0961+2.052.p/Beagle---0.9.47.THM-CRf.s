%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 180 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 424 expanded)
%              Number of equality atoms :   49 ( 159 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_86,axiom,(
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

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_653,plain,(
    ! [C_145,A_146,B_147] :
      ( m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ r1_tarski(k2_relat_1(C_145),B_147)
      | ~ r1_tarski(k1_relat_1(C_145),A_146)
      | ~ v1_relat_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_191,plain,(
    ! [C_51,A_52,B_53] :
      ( m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ r1_tarski(k2_relat_1(C_51),B_53)
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_226,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ r1_tarski(k2_relat_1(C_61),B_60)
      | ~ r1_tarski(k1_relat_1(C_61),A_59)
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_191,c_26])).

tff(c_234,plain,(
    ! [A_62,C_63] :
      ( k1_relset_1(A_62,k2_relat_1(C_63),C_63) = k1_relat_1(C_63)
      | ~ r1_tarski(k1_relat_1(C_63),A_62)
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_241,plain,(
    ! [C_63] :
      ( k1_relset_1(k1_relat_1(C_63),k2_relat_1(C_63),C_63) = k1_relat_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_89,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_94,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_28,plain,(
    ! [C_15,A_13,B_14] :
      ( m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ r1_tarski(k2_relat_1(C_15),B_14)
      | ~ r1_tarski(k1_relat_1(C_15),A_13)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_298,plain,(
    ! [B_70,C_71,A_72] :
      ( k1_xboole_0 = B_70
      | v1_funct_2(C_71,A_72,B_70)
      | k1_relset_1(A_72,B_70,C_71) != A_72
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_352,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_xboole_0 = B_82
      | v1_funct_2(C_83,A_84,B_82)
      | k1_relset_1(A_84,B_82,C_83) != A_84
      | ~ r1_tarski(k2_relat_1(C_83),B_82)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_28,c_298])).

tff(c_360,plain,(
    ! [C_85,A_86] :
      ( k2_relat_1(C_85) = k1_xboole_0
      | v1_funct_2(C_85,A_86,k2_relat_1(C_85))
      | k1_relset_1(A_86,k2_relat_1(C_85),C_85) != A_86
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_88,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_372,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_360,c_88])).

tff(c_384,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_372])).

tff(c_385,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_384])).

tff(c_389,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_385])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_389])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_408,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_20])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_406,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_14])).

tff(c_495,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_505,plain,(
    ! [A_103,B_104] : k1_relset_1(A_103,B_104,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_406,c_495])).

tff(c_507,plain,(
    ! [A_103,B_104] : k1_relset_1(A_103,B_104,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_505])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_545,plain,(
    ! [C_116,B_117] :
      ( v1_funct_2(C_116,'#skF_1',B_117)
      | k1_relset_1('#skF_1',B_117,C_116) != '#skF_1'
      | ~ m1_subset_1(C_116,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_394,c_394,c_52])).

tff(c_548,plain,(
    ! [B_117] :
      ( v1_funct_2('#skF_1','#skF_1',B_117)
      | k1_relset_1('#skF_1',B_117,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_406,c_545])).

tff(c_551,plain,(
    ! [B_117] : v1_funct_2('#skF_1','#skF_1',B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_548])).

tff(c_395,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_413,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_395])).

tff(c_414,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_88])).

tff(c_448,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_414])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_448])).

tff(c_569,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_661,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_653,c_569])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_6,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.68/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.39  
% 2.68/1.40  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.68/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.40  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.68/1.40  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.68/1.40  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.68/1.40  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.68/1.40  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.40  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.40  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.68/1.40  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.40  tff(c_653, plain, (![C_145, A_146, B_147]: (m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~r1_tarski(k2_relat_1(C_145), B_147) | ~r1_tarski(k1_relat_1(C_145), A_146) | ~v1_relat_1(C_145))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.40  tff(c_191, plain, (![C_51, A_52, B_53]: (m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~r1_tarski(k2_relat_1(C_51), B_53) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.40  tff(c_26, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.40  tff(c_226, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~r1_tarski(k2_relat_1(C_61), B_60) | ~r1_tarski(k1_relat_1(C_61), A_59) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_191, c_26])).
% 2.68/1.40  tff(c_234, plain, (![A_62, C_63]: (k1_relset_1(A_62, k2_relat_1(C_63), C_63)=k1_relat_1(C_63) | ~r1_tarski(k1_relat_1(C_63), A_62) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_6, c_226])).
% 2.68/1.40  tff(c_241, plain, (![C_63]: (k1_relset_1(k1_relat_1(C_63), k2_relat_1(C_63), C_63)=k1_relat_1(C_63) | ~v1_relat_1(C_63))), inference(resolution, [status(thm)], [c_6, c_234])).
% 2.68/1.40  tff(c_89, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.68/1.40  tff(c_93, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_89])).
% 2.68/1.40  tff(c_94, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_93])).
% 2.68/1.40  tff(c_28, plain, (![C_15, A_13, B_14]: (m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~r1_tarski(k2_relat_1(C_15), B_14) | ~r1_tarski(k1_relat_1(C_15), A_13) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.40  tff(c_298, plain, (![B_70, C_71, A_72]: (k1_xboole_0=B_70 | v1_funct_2(C_71, A_72, B_70) | k1_relset_1(A_72, B_70, C_71)!=A_72 | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.68/1.40  tff(c_352, plain, (![B_82, C_83, A_84]: (k1_xboole_0=B_82 | v1_funct_2(C_83, A_84, B_82) | k1_relset_1(A_84, B_82, C_83)!=A_84 | ~r1_tarski(k2_relat_1(C_83), B_82) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_28, c_298])).
% 2.68/1.40  tff(c_360, plain, (![C_85, A_86]: (k2_relat_1(C_85)=k1_xboole_0 | v1_funct_2(C_85, A_86, k2_relat_1(C_85)) | k1_relset_1(A_86, k2_relat_1(C_85), C_85)!=A_86 | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_6, c_352])).
% 2.68/1.40  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.40  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.40  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 2.68/1.40  tff(c_88, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.68/1.40  tff(c_372, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_360, c_88])).
% 2.68/1.40  tff(c_384, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_372])).
% 2.68/1.41  tff(c_385, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_94, c_384])).
% 2.68/1.41  tff(c_389, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_241, c_385])).
% 2.68/1.41  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_389])).
% 2.68/1.41  tff(c_394, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_93])).
% 2.68/1.41  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.41  tff(c_408, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_20])).
% 2.68/1.41  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.41  tff(c_406, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_14])).
% 2.68/1.41  tff(c_495, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.41  tff(c_505, plain, (![A_103, B_104]: (k1_relset_1(A_103, B_104, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_406, c_495])).
% 2.68/1.41  tff(c_507, plain, (![A_103, B_104]: (k1_relset_1(A_103, B_104, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_505])).
% 2.68/1.41  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.41  tff(c_34, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.68/1.41  tff(c_52, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 2.68/1.41  tff(c_545, plain, (![C_116, B_117]: (v1_funct_2(C_116, '#skF_1', B_117) | k1_relset_1('#skF_1', B_117, C_116)!='#skF_1' | ~m1_subset_1(C_116, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_394, c_394, c_52])).
% 2.68/1.41  tff(c_548, plain, (![B_117]: (v1_funct_2('#skF_1', '#skF_1', B_117) | k1_relset_1('#skF_1', B_117, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_406, c_545])).
% 2.68/1.41  tff(c_551, plain, (![B_117]: (v1_funct_2('#skF_1', '#skF_1', B_117))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_548])).
% 2.68/1.41  tff(c_395, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 2.68/1.41  tff(c_413, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_395])).
% 2.68/1.41  tff(c_414, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_88])).
% 2.68/1.41  tff(c_448, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_414])).
% 2.68/1.41  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_551, c_448])).
% 2.68/1.41  tff(c_569, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_48])).
% 2.68/1.41  tff(c_661, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_653, c_569])).
% 2.68/1.41  tff(c_673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_6, c_661])).
% 2.68/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.41  
% 2.68/1.41  Inference rules
% 2.68/1.41  ----------------------
% 2.68/1.41  #Ref     : 0
% 2.68/1.41  #Sup     : 124
% 2.68/1.41  #Fact    : 0
% 2.68/1.41  #Define  : 0
% 2.68/1.41  #Split   : 5
% 2.68/1.41  #Chain   : 0
% 2.68/1.41  #Close   : 0
% 2.68/1.41  
% 2.68/1.41  Ordering : KBO
% 2.68/1.41  
% 2.68/1.41  Simplification rules
% 2.68/1.41  ----------------------
% 2.68/1.41  #Subsume      : 4
% 2.68/1.41  #Demod        : 133
% 2.68/1.41  #Tautology    : 82
% 2.68/1.41  #SimpNegUnit  : 1
% 2.68/1.41  #BackRed      : 10
% 2.68/1.41  
% 2.68/1.41  #Partial instantiations: 0
% 2.68/1.41  #Strategies tried      : 1
% 2.68/1.41  
% 2.68/1.41  Timing (in seconds)
% 2.68/1.41  ----------------------
% 2.68/1.41  Preprocessing        : 0.32
% 2.68/1.41  Parsing              : 0.17
% 2.68/1.41  CNF conversion       : 0.02
% 2.68/1.41  Main loop            : 0.31
% 2.68/1.41  Inferencing          : 0.11
% 2.68/1.41  Reduction            : 0.09
% 2.68/1.41  Demodulation         : 0.07
% 2.68/1.41  BG Simplification    : 0.02
% 2.68/1.41  Subsumption          : 0.06
% 2.68/1.41  Abstraction          : 0.02
% 2.68/1.41  MUC search           : 0.00
% 2.68/1.41  Cooper               : 0.00
% 2.68/1.41  Total                : 0.66
% 2.68/1.41  Index Insertion      : 0.00
% 2.68/1.41  Index Deletion       : 0.00
% 2.68/1.41  Index Matching       : 0.00
% 2.68/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
