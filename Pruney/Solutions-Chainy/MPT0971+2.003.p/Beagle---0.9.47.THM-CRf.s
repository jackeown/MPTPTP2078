%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 123 expanded)
%              Number of leaves         :   39 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 268 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_90,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_90])).

tff(c_74,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_83,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_165,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_156])).

tff(c_56,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_107,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ v1_xboole_0(C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [B_89,A_90,A_91] :
      ( ~ v1_xboole_0(B_89)
      | ~ r2_hidden(A_90,A_91)
      | ~ r1_tarski(A_91,B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_133,plain,(
    ! [B_89] :
      ( ~ v1_xboole_0(B_89)
      | ~ r1_tarski(k2_relset_1('#skF_5','#skF_6','#skF_8'),B_89) ) ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_175,plain,(
    ! [B_102] :
      ( ~ v1_xboole_0(B_102)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_133])).

tff(c_179,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(A_6)
      | ~ v5_relat_1('#skF_8',A_6)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_175])).

tff(c_183,plain,(
    ! [A_103] :
      ( ~ v1_xboole_0(A_103)
      | ~ v5_relat_1('#skF_8',A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_179])).

tff(c_187,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_99,c_183])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_208,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_relset_1(A_118,B_119,C_120) = k1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_217,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_208])).

tff(c_319,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_326,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_319])).

tff(c_330,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_217,c_326])).

tff(c_331,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_18,plain,(
    ! [A_8,C_44] :
      ( r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_339,plain,(
    ! [C_44] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_44),'#skF_5')
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_18])).

tff(c_372,plain,(
    ! [C_170] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_170),'#skF_5')
      | ~ r2_hidden(C_170,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_62,c_339])).

tff(c_54,plain,(
    ! [E_64] :
      ( k1_funct_1('#skF_8',E_64) != '#skF_7'
      | ~ r2_hidden(E_64,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_380,plain,(
    ! [C_171] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_171)) != '#skF_7'
      | ~ r2_hidden(C_171,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_372,c_54])).

tff(c_384,plain,(
    ! [C_44] :
      ( C_44 != '#skF_7'
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_380])).

tff(c_387,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_62,c_384])).

tff(c_167,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_56])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_167])).

tff(c_390,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_402,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_2])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.59/1.36  
% 2.59/1.36  %Foreground sorts:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Background operators:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Foreground operators:
% 2.59/1.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.59/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.59/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.59/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.59/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.59/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.59/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.36  
% 2.79/1.37  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.79/1.37  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.37  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.79/1.37  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.37  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.37  tff(f_37, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.79/1.37  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.79/1.37  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.37  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.79/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.79/1.37  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.37  tff(c_90, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.37  tff(c_99, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_90])).
% 2.79/1.37  tff(c_74, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.37  tff(c_83, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_74])).
% 2.79/1.37  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.37  tff(c_156, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.37  tff(c_165, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_156])).
% 2.79/1.37  tff(c_56, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.37  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.79/1.37  tff(c_107, plain, (![C_84, B_85, A_86]: (~v1_xboole_0(C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.37  tff(c_130, plain, (![B_89, A_90, A_91]: (~v1_xboole_0(B_89) | ~r2_hidden(A_90, A_91) | ~r1_tarski(A_91, B_89))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.79/1.38  tff(c_133, plain, (![B_89]: (~v1_xboole_0(B_89) | ~r1_tarski(k2_relset_1('#skF_5', '#skF_6', '#skF_8'), B_89))), inference(resolution, [status(thm)], [c_56, c_130])).
% 2.79/1.38  tff(c_175, plain, (![B_102]: (~v1_xboole_0(B_102) | ~r1_tarski(k2_relat_1('#skF_8'), B_102))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_133])).
% 2.79/1.38  tff(c_179, plain, (![A_6]: (~v1_xboole_0(A_6) | ~v5_relat_1('#skF_8', A_6) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_175])).
% 2.79/1.38  tff(c_183, plain, (![A_103]: (~v1_xboole_0(A_103) | ~v5_relat_1('#skF_8', A_103))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_179])).
% 2.79/1.38  tff(c_187, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_99, c_183])).
% 2.79/1.38  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.38  tff(c_16, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.79/1.38  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.38  tff(c_208, plain, (![A_118, B_119, C_120]: (k1_relset_1(A_118, B_119, C_120)=k1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.38  tff(c_217, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_208])).
% 2.79/1.38  tff(c_319, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.79/1.38  tff(c_326, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_319])).
% 2.79/1.38  tff(c_330, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_217, c_326])).
% 2.79/1.38  tff(c_331, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_330])).
% 2.79/1.38  tff(c_18, plain, (![A_8, C_44]: (r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.79/1.38  tff(c_339, plain, (![C_44]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_44), '#skF_5') | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_18])).
% 2.79/1.38  tff(c_372, plain, (![C_170]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_170), '#skF_5') | ~r2_hidden(C_170, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_62, c_339])).
% 2.79/1.38  tff(c_54, plain, (![E_64]: (k1_funct_1('#skF_8', E_64)!='#skF_7' | ~r2_hidden(E_64, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.38  tff(c_380, plain, (![C_171]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_171))!='#skF_7' | ~r2_hidden(C_171, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_372, c_54])).
% 2.79/1.38  tff(c_384, plain, (![C_44]: (C_44!='#skF_7' | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_380])).
% 2.79/1.38  tff(c_387, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_62, c_384])).
% 2.79/1.38  tff(c_167, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_56])).
% 2.79/1.38  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_167])).
% 2.79/1.38  tff(c_390, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_330])).
% 2.79/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.79/1.38  tff(c_402, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_2])).
% 2.79/1.38  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_402])).
% 2.79/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  Inference rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Ref     : 0
% 2.79/1.38  #Sup     : 65
% 2.79/1.38  #Fact    : 0
% 2.79/1.38  #Define  : 0
% 2.79/1.38  #Split   : 3
% 2.79/1.38  #Chain   : 0
% 2.79/1.38  #Close   : 0
% 2.79/1.38  
% 2.79/1.38  Ordering : KBO
% 2.79/1.38  
% 2.79/1.38  Simplification rules
% 2.79/1.38  ----------------------
% 2.79/1.38  #Subsume      : 6
% 2.79/1.38  #Demod        : 59
% 2.79/1.38  #Tautology    : 19
% 2.79/1.38  #SimpNegUnit  : 3
% 2.79/1.38  #BackRed      : 15
% 2.79/1.38  
% 2.79/1.38  #Partial instantiations: 0
% 2.79/1.38  #Strategies tried      : 1
% 2.79/1.38  
% 2.79/1.38  Timing (in seconds)
% 2.79/1.38  ----------------------
% 2.79/1.38  Preprocessing        : 0.34
% 2.79/1.38  Parsing              : 0.18
% 2.79/1.38  CNF conversion       : 0.03
% 2.79/1.38  Main loop            : 0.26
% 2.79/1.38  Inferencing          : 0.10
% 2.79/1.38  Reduction            : 0.07
% 2.79/1.38  Demodulation         : 0.05
% 2.79/1.38  BG Simplification    : 0.02
% 2.79/1.38  Subsumption          : 0.05
% 2.79/1.38  Abstraction          : 0.02
% 2.79/1.38  MUC search           : 0.00
% 2.79/1.38  Cooper               : 0.00
% 2.79/1.38  Total                : 0.64
% 2.79/1.38  Index Insertion      : 0.00
% 2.79/1.38  Index Deletion       : 0.00
% 2.79/1.38  Index Matching       : 0.00
% 2.79/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
