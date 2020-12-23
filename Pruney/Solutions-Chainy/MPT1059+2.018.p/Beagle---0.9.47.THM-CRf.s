%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 305 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_110,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_297,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_310,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_297])).

tff(c_979,plain,(
    ! [B_161,A_162,C_163] :
      ( k1_xboole_0 = B_161
      | k1_relset_1(A_162,B_161,C_163) = A_162
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_986,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_979])).

tff(c_994,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_310,c_986])).

tff(c_996,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_1330,plain,(
    ! [A_181,B_182,C_183] :
      ( k7_partfun1(A_181,B_182,C_183) = k1_funct_1(B_182,C_183)
      | ~ r2_hidden(C_183,k1_relat_1(B_182))
      | ~ v1_funct_1(B_182)
      | ~ v5_relat_1(B_182,A_181)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1332,plain,(
    ! [A_181,C_183] :
      ( k7_partfun1(A_181,'#skF_4',C_183) = k1_funct_1('#skF_4',C_183)
      | ~ r2_hidden(C_183,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_181)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_1330])).

tff(c_1339,plain,(
    ! [A_184,C_185] :
      ( k7_partfun1(A_184,'#skF_4',C_185) = k1_funct_1('#skF_4',C_185)
      | ~ r2_hidden(C_185,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_48,c_1332])).

tff(c_1342,plain,(
    ! [A_184,A_7] :
      ( k7_partfun1(A_184,'#skF_4',A_7) = k1_funct_1('#skF_4',A_7)
      | ~ v5_relat_1('#skF_4',A_184)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1339])).

tff(c_1346,plain,(
    ! [A_186,A_187] :
      ( k7_partfun1(A_186,'#skF_4',A_187) = k1_funct_1('#skF_4',A_187)
      | ~ v5_relat_1('#skF_4',A_186)
      | ~ m1_subset_1(A_187,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1342])).

tff(c_1354,plain,(
    ! [A_188] :
      ( k7_partfun1('#skF_3','#skF_4',A_188) = k1_funct_1('#skF_4',A_188)
      | ~ m1_subset_1(A_188,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_123,c_1346])).

tff(c_1363,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1354])).

tff(c_40,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1364,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_40])).

tff(c_1480,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( k3_funct_2(A_192,B_193,C_194,D_195) = k1_funct_1(C_194,D_195)
      | ~ m1_subset_1(D_195,A_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(C_194,A_192,B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1490,plain,(
    ! [B_193,C_194] :
      ( k3_funct_2('#skF_2',B_193,C_194,'#skF_5') = k1_funct_1(C_194,'#skF_5')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_193)))
      | ~ v1_funct_2(C_194,'#skF_2',B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_1480])).

tff(c_1533,plain,(
    ! [B_197,C_198] :
      ( k3_funct_2('#skF_2',B_197,C_198,'#skF_5') = k1_funct_1(C_198,'#skF_5')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_197)))
      | ~ v1_funct_2(C_198,'#skF_2',B_197)
      | ~ v1_funct_1(C_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1490])).

tff(c_1540,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1533])).

tff(c_1548,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1540])).

tff(c_1550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1364,c_1548])).

tff(c_1551,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_126,plain,(
    ! [B_68,A_69] :
      ( ~ r1_tarski(B_68,A_69)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_87,c_14])).

tff(c_138,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_150,plain,(
    ! [A_73] : ~ m1_subset_1(A_73,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_155,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_156,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1581,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_156])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.59  
% 3.69/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.69/1.59  
% 3.69/1.59  %Foreground sorts:
% 3.69/1.59  
% 3.69/1.59  
% 3.69/1.59  %Background operators:
% 3.69/1.59  
% 3.69/1.59  
% 3.69/1.59  %Foreground operators:
% 3.69/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.59  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.69/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.69/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.69/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.69/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.59  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.69/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.59  
% 3.84/1.61  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 3.84/1.61  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.84/1.61  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.84/1.61  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.84/1.61  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.84/1.61  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.84/1.61  tff(f_94, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.84/1.61  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.84/1.61  tff(f_36, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.84/1.61  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.84/1.61  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.84/1.61  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_110, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.84/1.61  tff(c_123, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_110])).
% 3.84/1.61  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.84/1.61  tff(c_72, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.84/1.61  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_72])).
% 3.84/1.61  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_297, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.84/1.61  tff(c_310, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_297])).
% 3.84/1.61  tff(c_979, plain, (![B_161, A_162, C_163]: (k1_xboole_0=B_161 | k1_relset_1(A_162, B_161, C_163)=A_162 | ~v1_funct_2(C_163, A_162, B_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.84/1.61  tff(c_986, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_979])).
% 3.84/1.61  tff(c_994, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_310, c_986])).
% 3.84/1.61  tff(c_996, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_994])).
% 3.84/1.61  tff(c_1330, plain, (![A_181, B_182, C_183]: (k7_partfun1(A_181, B_182, C_183)=k1_funct_1(B_182, C_183) | ~r2_hidden(C_183, k1_relat_1(B_182)) | ~v1_funct_1(B_182) | ~v5_relat_1(B_182, A_181) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.84/1.61  tff(c_1332, plain, (![A_181, C_183]: (k7_partfun1(A_181, '#skF_4', C_183)=k1_funct_1('#skF_4', C_183) | ~r2_hidden(C_183, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_181) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_996, c_1330])).
% 3.84/1.61  tff(c_1339, plain, (![A_184, C_185]: (k7_partfun1(A_184, '#skF_4', C_185)=k1_funct_1('#skF_4', C_185) | ~r2_hidden(C_185, '#skF_2') | ~v5_relat_1('#skF_4', A_184))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_48, c_1332])).
% 3.84/1.61  tff(c_1342, plain, (![A_184, A_7]: (k7_partfun1(A_184, '#skF_4', A_7)=k1_funct_1('#skF_4', A_7) | ~v5_relat_1('#skF_4', A_184) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1339])).
% 3.84/1.61  tff(c_1346, plain, (![A_186, A_187]: (k7_partfun1(A_186, '#skF_4', A_187)=k1_funct_1('#skF_4', A_187) | ~v5_relat_1('#skF_4', A_186) | ~m1_subset_1(A_187, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1342])).
% 3.84/1.61  tff(c_1354, plain, (![A_188]: (k7_partfun1('#skF_3', '#skF_4', A_188)=k1_funct_1('#skF_4', A_188) | ~m1_subset_1(A_188, '#skF_2'))), inference(resolution, [status(thm)], [c_123, c_1346])).
% 3.84/1.61  tff(c_1363, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_1354])).
% 3.84/1.61  tff(c_40, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.84/1.61  tff(c_1364, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1363, c_40])).
% 3.84/1.61  tff(c_1480, plain, (![A_192, B_193, C_194, D_195]: (k3_funct_2(A_192, B_193, C_194, D_195)=k1_funct_1(C_194, D_195) | ~m1_subset_1(D_195, A_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(C_194, A_192, B_193) | ~v1_funct_1(C_194) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.84/1.61  tff(c_1490, plain, (![B_193, C_194]: (k3_funct_2('#skF_2', B_193, C_194, '#skF_5')=k1_funct_1(C_194, '#skF_5') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_193))) | ~v1_funct_2(C_194, '#skF_2', B_193) | ~v1_funct_1(C_194) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_1480])).
% 3.84/1.61  tff(c_1533, plain, (![B_197, C_198]: (k3_funct_2('#skF_2', B_197, C_198, '#skF_5')=k1_funct_1(C_198, '#skF_5') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_197))) | ~v1_funct_2(C_198, '#skF_2', B_197) | ~v1_funct_1(C_198))), inference(negUnitSimplification, [status(thm)], [c_52, c_1490])).
% 3.84/1.61  tff(c_1540, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1533])).
% 3.84/1.61  tff(c_1548, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1540])).
% 3.84/1.61  tff(c_1550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1364, c_1548])).
% 3.84/1.61  tff(c_1551, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_994])).
% 3.84/1.61  tff(c_6, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.84/1.61  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.61  tff(c_87, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | v1_xboole_0(B_57) | ~m1_subset_1(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.84/1.61  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.61  tff(c_126, plain, (![B_68, A_69]: (~r1_tarski(B_68, A_69) | v1_xboole_0(B_68) | ~m1_subset_1(A_69, B_68))), inference(resolution, [status(thm)], [c_87, c_14])).
% 3.84/1.61  tff(c_138, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_126])).
% 3.84/1.61  tff(c_150, plain, (![A_73]: (~m1_subset_1(A_73, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_138])).
% 3.84/1.61  tff(c_155, plain, $false, inference(resolution, [status(thm)], [c_6, c_150])).
% 3.84/1.61  tff(c_156, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 3.84/1.61  tff(c_1581, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_156])).
% 3.84/1.61  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1581])).
% 3.84/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.61  
% 3.84/1.61  Inference rules
% 3.84/1.61  ----------------------
% 3.84/1.61  #Ref     : 0
% 3.84/1.61  #Sup     : 301
% 3.84/1.61  #Fact    : 0
% 3.84/1.61  #Define  : 0
% 3.84/1.61  #Split   : 5
% 3.84/1.61  #Chain   : 0
% 3.84/1.61  #Close   : 0
% 3.84/1.61  
% 3.84/1.61  Ordering : KBO
% 3.84/1.61  
% 3.84/1.61  Simplification rules
% 3.84/1.61  ----------------------
% 3.84/1.61  #Subsume      : 13
% 3.84/1.61  #Demod        : 239
% 3.84/1.61  #Tautology    : 131
% 3.84/1.61  #SimpNegUnit  : 4
% 3.84/1.61  #BackRed      : 54
% 3.84/1.61  
% 3.84/1.61  #Partial instantiations: 0
% 3.84/1.61  #Strategies tried      : 1
% 3.84/1.61  
% 3.84/1.61  Timing (in seconds)
% 3.84/1.61  ----------------------
% 3.84/1.61  Preprocessing        : 0.32
% 3.84/1.61  Parsing              : 0.16
% 3.84/1.61  CNF conversion       : 0.02
% 3.84/1.61  Main loop            : 0.52
% 3.84/1.61  Inferencing          : 0.18
% 3.84/1.61  Reduction            : 0.18
% 3.84/1.61  Demodulation         : 0.13
% 3.84/1.61  BG Simplification    : 0.03
% 3.84/1.61  Subsumption          : 0.09
% 3.84/1.61  Abstraction          : 0.02
% 3.84/1.61  MUC search           : 0.00
% 3.84/1.61  Cooper               : 0.00
% 3.84/1.61  Total                : 0.88
% 3.84/1.61  Index Insertion      : 0.00
% 3.84/1.61  Index Deletion       : 0.00
% 3.84/1.61  Index Matching       : 0.00
% 3.84/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
