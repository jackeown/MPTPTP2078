%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 583 expanded)
%              Number of leaves         :   42 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 (1613 expanded)
%              Number of equality atoms :   54 ( 537 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_109,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_24,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_129,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_129])).

tff(c_138,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_132])).

tff(c_1241,plain,(
    ! [C_199,B_200,A_201] :
      ( v5_relat_1(C_199,B_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1255,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1241])).

tff(c_1311,plain,(
    ! [B_216,A_217] :
      ( r1_tarski(k2_relat_1(B_216),A_217)
      | ~ v5_relat_1(B_216,A_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1257,plain,(
    ! [A_202,C_203,B_204] :
      ( r1_tarski(A_202,C_203)
      | ~ r1_tarski(B_204,C_203)
      | ~ r1_tarski(A_202,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1263,plain,(
    ! [A_202] :
      ( r1_tarski(A_202,'#skF_4')
      | ~ r1_tarski(A_202,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_1257])).

tff(c_1322,plain,(
    ! [B_216] :
      ( r1_tarski(k2_relat_1(B_216),'#skF_4')
      | ~ v5_relat_1(B_216,'#skF_3')
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_1311,c_1263])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1794,plain,(
    ! [A_272,B_273,C_274] :
      ( k1_relset_1(A_272,B_273,C_274) = k1_relat_1(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1808,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1794])).

tff(c_2297,plain,(
    ! [B_322,A_323,C_324] :
      ( k1_xboole_0 = B_322
      | k1_relset_1(A_323,B_322,C_324) = A_323
      | ~ v1_funct_2(C_324,A_323,B_322)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2306,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2297])).

tff(c_2318,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1808,c_2306])).

tff(c_2319,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2318])).

tff(c_56,plain,(
    ! [B_54,A_53] :
      ( m1_subset_1(B_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_54),A_53)))
      | ~ r1_tarski(k2_relat_1(B_54),A_53)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2336,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_53)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_53)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2319,c_56])).

tff(c_2445,plain,(
    ! [A_334] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_334)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_72,c_2336])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_141,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_143,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_143])).

tff(c_229,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v5_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_160,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(A_75,C_76)
      | ~ r1_tarski(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,'#skF_4')
      | ~ r1_tarski(A_75,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_160])).

tff(c_240,plain,(
    ! [B_89] :
      ( r1_tarski(k2_relat_1(B_89),'#skF_4')
      | ~ v5_relat_1(B_89,'#skF_3')
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_229,c_166])).

tff(c_677,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_691,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_677])).

tff(c_1159,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1168,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1159])).

tff(c_1180,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_691,c_1168])).

tff(c_1181,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1180])).

tff(c_58,plain,(
    ! [B_54,A_53] :
      ( v1_funct_2(B_54,k1_relat_1(B_54),A_53)
      | ~ r1_tarski(k2_relat_1(B_54),A_53)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1201,plain,(
    ! [A_53] :
      ( v1_funct_2('#skF_5','#skF_2',A_53)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_53)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1181,c_58])).

tff(c_1217,plain,(
    ! [A_196] :
      ( v1_funct_2('#skF_5','#skF_2',A_196)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_72,c_1201])).

tff(c_1225,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_240,c_1217])).

tff(c_1235,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_157,c_1225])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_1235])).

tff(c_1238,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2484,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2445,c_1238])).

tff(c_2493,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1322,c_2484])).

tff(c_2503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1255,c_2493])).

tff(c_2505,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2523,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_2505,c_8])).

tff(c_2531,plain,(
    ! [A_336,B_337] : v1_relat_1(k2_zfmisc_1(A_336,B_337)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2533,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2523,c_2531])).

tff(c_38,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2556,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | A_32 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_38])).

tff(c_2504,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2511,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_2504])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2506,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_2])).

tff(c_2516,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2506])).

tff(c_2517,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_68])).

tff(c_2534,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2517])).

tff(c_2640,plain,(
    ! [C_367,B_368,A_369] :
      ( ~ v1_xboole_0(C_367)
      | ~ m1_subset_1(B_368,k1_zfmisc_1(C_367))
      | ~ r2_hidden(A_369,B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2644,plain,(
    ! [A_369] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_369,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2534,c_2640])).

tff(c_2649,plain,(
    ! [A_370] : ~ r2_hidden(A_370,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2644])).

tff(c_2654,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2556,c_2649])).

tff(c_2661,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_72])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2535,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_12])).

tff(c_2669,plain,(
    ! [C_371,A_372,B_373] :
      ( v4_relat_1(C_371,A_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_372,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2681,plain,(
    ! [A_374] : v4_relat_1('#skF_3',A_374) ),
    inference(resolution,[status(thm)],[c_2535,c_2669])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ v4_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2684,plain,(
    ! [A_374] :
      ( k7_relat_1('#skF_3',A_374) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2681,c_26])).

tff(c_2695,plain,(
    ! [A_376] : k7_relat_1('#skF_3',A_376) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2684])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2708,plain,(
    ! [A_376] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_376)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2695,c_28])).

tff(c_2723,plain,(
    ! [A_377] : r1_tarski(k1_relat_1('#skF_3'),A_377) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2708])).

tff(c_2560,plain,(
    ! [B_342,A_343] :
      ( ~ r1_tarski(B_342,A_343)
      | ~ r2_hidden(A_343,B_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2564,plain,(
    ! [A_32] :
      ( ~ r1_tarski(A_32,'#skF_1'(A_32))
      | A_32 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2556,c_2560])).

tff(c_2743,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2723,c_2564])).

tff(c_2717,plain,(
    ! [A_376] : r1_tarski(k1_relat_1('#skF_3'),A_376) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2708])).

tff(c_2744,plain,(
    ! [A_376] : r1_tarski('#skF_3',A_376) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2743,c_2717])).

tff(c_2611,plain,(
    ! [C_358,B_359,A_360] :
      ( v5_relat_1(C_358,B_359)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_360,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2622,plain,(
    ! [B_359] : v5_relat_1('#skF_3',B_359) ),
    inference(resolution,[status(thm)],[c_2535,c_2611])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2750,plain,(
    ! [A_378] : r1_tarski('#skF_3',A_378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2743,c_2717])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2791,plain,(
    ! [A_381,A_382] :
      ( r1_tarski(A_381,A_382)
      | ~ r1_tarski(A_381,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2750,c_4])).

tff(c_2885,plain,(
    ! [B_392,A_393] :
      ( r1_tarski(k2_relat_1(B_392),A_393)
      | ~ v5_relat_1(B_392,'#skF_3')
      | ~ v1_relat_1(B_392) ) ),
    inference(resolution,[status(thm)],[c_22,c_2791])).

tff(c_2941,plain,(
    ! [B_398] :
      ( k2_relat_1(B_398) = '#skF_3'
      | ~ v5_relat_1(B_398,'#skF_3')
      | ~ v1_relat_1(B_398) ) ),
    inference(resolution,[status(thm)],[c_2885,c_2564])).

tff(c_2945,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2622,c_2941])).

tff(c_2948,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2945])).

tff(c_3200,plain,(
    ! [B_448,A_449] :
      ( v1_funct_2(B_448,k1_relat_1(B_448),A_449)
      | ~ r1_tarski(k2_relat_1(B_448),A_449)
      | ~ v1_funct_1(B_448)
      | ~ v1_relat_1(B_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3209,plain,(
    ! [A_449] :
      ( v1_funct_2('#skF_3','#skF_3',A_449)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_449)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2743,c_3200])).

tff(c_3212,plain,(
    ! [A_449] : v1_funct_2('#skF_3','#skF_3',A_449) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2661,c_2744,c_2948,c_3209])).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2537,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_2505,c_10])).

tff(c_2591,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2534,c_2537,c_2511,c_74])).

tff(c_2657,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2591])).

tff(c_3216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3212,c_2657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:19:37 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.76  
% 4.53/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.53/1.76  
% 4.53/1.76  %Foreground sorts:
% 4.53/1.76  
% 4.53/1.76  
% 4.53/1.76  %Background operators:
% 4.53/1.76  
% 4.53/1.76  
% 4.53/1.76  %Foreground operators:
% 4.53/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.53/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.53/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.53/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.53/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.53/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.53/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.53/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.53/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.53/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.53/1.76  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.53/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.53/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.53/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.76  
% 4.77/1.78  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.77/1.78  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 4.77/1.78  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.77/1.78  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.77/1.78  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.77/1.78  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.77/1.78  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.77/1.78  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.77/1.78  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.77/1.78  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.77/1.78  tff(f_109, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 4.77/1.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.77/1.78  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.77/1.78  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.77/1.78  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.77/1.78  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.77/1.78  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.77/1.78  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.78  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_129, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.77/1.78  tff(c_132, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_129])).
% 4.77/1.78  tff(c_138, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_132])).
% 4.77/1.78  tff(c_1241, plain, (![C_199, B_200, A_201]: (v5_relat_1(C_199, B_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.78  tff(c_1255, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1241])).
% 4.77/1.78  tff(c_1311, plain, (![B_216, A_217]: (r1_tarski(k2_relat_1(B_216), A_217) | ~v5_relat_1(B_216, A_217) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.77/1.78  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_1257, plain, (![A_202, C_203, B_204]: (r1_tarski(A_202, C_203) | ~r1_tarski(B_204, C_203) | ~r1_tarski(A_202, B_204))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.78  tff(c_1263, plain, (![A_202]: (r1_tarski(A_202, '#skF_4') | ~r1_tarski(A_202, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_1257])).
% 4.77/1.78  tff(c_1322, plain, (![B_216]: (r1_tarski(k2_relat_1(B_216), '#skF_4') | ~v5_relat_1(B_216, '#skF_3') | ~v1_relat_1(B_216))), inference(resolution, [status(thm)], [c_1311, c_1263])).
% 4.77/1.78  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_64, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_80, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_64])).
% 4.77/1.78  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_1794, plain, (![A_272, B_273, C_274]: (k1_relset_1(A_272, B_273, C_274)=k1_relat_1(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.77/1.78  tff(c_1808, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_1794])).
% 4.77/1.78  tff(c_2297, plain, (![B_322, A_323, C_324]: (k1_xboole_0=B_322 | k1_relset_1(A_323, B_322, C_324)=A_323 | ~v1_funct_2(C_324, A_323, B_322) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.77/1.78  tff(c_2306, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_2297])).
% 4.77/1.78  tff(c_2318, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1808, c_2306])).
% 4.77/1.78  tff(c_2319, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_80, c_2318])).
% 4.77/1.78  tff(c_56, plain, (![B_54, A_53]: (m1_subset_1(B_54, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_54), A_53))) | ~r1_tarski(k2_relat_1(B_54), A_53) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.77/1.78  tff(c_2336, plain, (![A_53]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_53))) | ~r1_tarski(k2_relat_1('#skF_5'), A_53) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2319, c_56])).
% 4.77/1.78  tff(c_2445, plain, (![A_334]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_334))) | ~r1_tarski(k2_relat_1('#skF_5'), A_334))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_72, c_2336])).
% 4.77/1.78  tff(c_62, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.77/1.78  tff(c_74, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 4.77/1.78  tff(c_141, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 4.77/1.78  tff(c_143, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.78  tff(c_157, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_143])).
% 4.77/1.78  tff(c_229, plain, (![B_89, A_90]: (r1_tarski(k2_relat_1(B_89), A_90) | ~v5_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.77/1.78  tff(c_160, plain, (![A_75, C_76, B_77]: (r1_tarski(A_75, C_76) | ~r1_tarski(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.78  tff(c_166, plain, (![A_75]: (r1_tarski(A_75, '#skF_4') | ~r1_tarski(A_75, '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_160])).
% 4.77/1.78  tff(c_240, plain, (![B_89]: (r1_tarski(k2_relat_1(B_89), '#skF_4') | ~v5_relat_1(B_89, '#skF_3') | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_229, c_166])).
% 4.77/1.78  tff(c_677, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.77/1.78  tff(c_691, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_677])).
% 4.77/1.78  tff(c_1159, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.77/1.78  tff(c_1168, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1159])).
% 4.77/1.78  tff(c_1180, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_691, c_1168])).
% 4.77/1.78  tff(c_1181, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_80, c_1180])).
% 4.77/1.78  tff(c_58, plain, (![B_54, A_53]: (v1_funct_2(B_54, k1_relat_1(B_54), A_53) | ~r1_tarski(k2_relat_1(B_54), A_53) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.77/1.78  tff(c_1201, plain, (![A_53]: (v1_funct_2('#skF_5', '#skF_2', A_53) | ~r1_tarski(k2_relat_1('#skF_5'), A_53) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1181, c_58])).
% 4.77/1.78  tff(c_1217, plain, (![A_196]: (v1_funct_2('#skF_5', '#skF_2', A_196) | ~r1_tarski(k2_relat_1('#skF_5'), A_196))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_72, c_1201])).
% 4.77/1.78  tff(c_1225, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_240, c_1217])).
% 4.77/1.78  tff(c_1235, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_157, c_1225])).
% 4.77/1.78  tff(c_1237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_1235])).
% 4.77/1.78  tff(c_1238, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_74])).
% 4.77/1.78  tff(c_2484, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2445, c_1238])).
% 4.77/1.79  tff(c_2493, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1322, c_2484])).
% 4.77/1.79  tff(c_2503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_1255, c_2493])).
% 4.77/1.79  tff(c_2505, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_64])).
% 4.77/1.79  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.77/1.79  tff(c_2523, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_2505, c_8])).
% 4.77/1.79  tff(c_2531, plain, (![A_336, B_337]: (v1_relat_1(k2_zfmisc_1(A_336, B_337)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.77/1.79  tff(c_2533, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2523, c_2531])).
% 4.77/1.79  tff(c_38, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.79  tff(c_2556, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | A_32='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_38])).
% 4.77/1.79  tff(c_2504, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 4.77/1.79  tff(c_2511, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_2504])).
% 4.77/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.77/1.79  tff(c_2506, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_2])).
% 4.77/1.79  tff(c_2516, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2506])).
% 4.77/1.79  tff(c_2517, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_68])).
% 4.77/1.79  tff(c_2534, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2517])).
% 4.77/1.79  tff(c_2640, plain, (![C_367, B_368, A_369]: (~v1_xboole_0(C_367) | ~m1_subset_1(B_368, k1_zfmisc_1(C_367)) | ~r2_hidden(A_369, B_368))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.79  tff(c_2644, plain, (![A_369]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_369, '#skF_5'))), inference(resolution, [status(thm)], [c_2534, c_2640])).
% 4.77/1.79  tff(c_2649, plain, (![A_370]: (~r2_hidden(A_370, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2644])).
% 4.77/1.79  tff(c_2654, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2556, c_2649])).
% 4.77/1.79  tff(c_2661, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_72])).
% 4.77/1.79  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.77/1.79  tff(c_2535, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_12])).
% 4.77/1.79  tff(c_2669, plain, (![C_371, A_372, B_373]: (v4_relat_1(C_371, A_372) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_372, B_373))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.79  tff(c_2681, plain, (![A_374]: (v4_relat_1('#skF_3', A_374))), inference(resolution, [status(thm)], [c_2535, c_2669])).
% 4.77/1.79  tff(c_26, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~v4_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.77/1.79  tff(c_2684, plain, (![A_374]: (k7_relat_1('#skF_3', A_374)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2681, c_26])).
% 4.77/1.79  tff(c_2695, plain, (![A_376]: (k7_relat_1('#skF_3', A_376)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2684])).
% 4.77/1.79  tff(c_28, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.79  tff(c_2708, plain, (![A_376]: (r1_tarski(k1_relat_1('#skF_3'), A_376) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2695, c_28])).
% 4.77/1.79  tff(c_2723, plain, (![A_377]: (r1_tarski(k1_relat_1('#skF_3'), A_377))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2708])).
% 4.77/1.79  tff(c_2560, plain, (![B_342, A_343]: (~r1_tarski(B_342, A_343) | ~r2_hidden(A_343, B_342))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.77/1.79  tff(c_2564, plain, (![A_32]: (~r1_tarski(A_32, '#skF_1'(A_32)) | A_32='#skF_3')), inference(resolution, [status(thm)], [c_2556, c_2560])).
% 4.77/1.79  tff(c_2743, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2723, c_2564])).
% 4.77/1.79  tff(c_2717, plain, (![A_376]: (r1_tarski(k1_relat_1('#skF_3'), A_376))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2708])).
% 4.77/1.79  tff(c_2744, plain, (![A_376]: (r1_tarski('#skF_3', A_376))), inference(demodulation, [status(thm), theory('equality')], [c_2743, c_2717])).
% 4.77/1.79  tff(c_2611, plain, (![C_358, B_359, A_360]: (v5_relat_1(C_358, B_359) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_360, B_359))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.77/1.79  tff(c_2622, plain, (![B_359]: (v5_relat_1('#skF_3', B_359))), inference(resolution, [status(thm)], [c_2535, c_2611])).
% 4.77/1.79  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.77/1.79  tff(c_2750, plain, (![A_378]: (r1_tarski('#skF_3', A_378))), inference(demodulation, [status(thm), theory('equality')], [c_2743, c_2717])).
% 4.77/1.79  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.79  tff(c_2791, plain, (![A_381, A_382]: (r1_tarski(A_381, A_382) | ~r1_tarski(A_381, '#skF_3'))), inference(resolution, [status(thm)], [c_2750, c_4])).
% 4.77/1.79  tff(c_2885, plain, (![B_392, A_393]: (r1_tarski(k2_relat_1(B_392), A_393) | ~v5_relat_1(B_392, '#skF_3') | ~v1_relat_1(B_392))), inference(resolution, [status(thm)], [c_22, c_2791])).
% 4.77/1.79  tff(c_2941, plain, (![B_398]: (k2_relat_1(B_398)='#skF_3' | ~v5_relat_1(B_398, '#skF_3') | ~v1_relat_1(B_398))), inference(resolution, [status(thm)], [c_2885, c_2564])).
% 4.77/1.79  tff(c_2945, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2622, c_2941])).
% 4.77/1.79  tff(c_2948, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2945])).
% 4.77/1.79  tff(c_3200, plain, (![B_448, A_449]: (v1_funct_2(B_448, k1_relat_1(B_448), A_449) | ~r1_tarski(k2_relat_1(B_448), A_449) | ~v1_funct_1(B_448) | ~v1_relat_1(B_448))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.77/1.79  tff(c_3209, plain, (![A_449]: (v1_funct_2('#skF_3', '#skF_3', A_449) | ~r1_tarski(k2_relat_1('#skF_3'), A_449) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2743, c_3200])).
% 4.77/1.79  tff(c_3212, plain, (![A_449]: (v1_funct_2('#skF_3', '#skF_3', A_449))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2661, c_2744, c_2948, c_3209])).
% 4.77/1.79  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.77/1.79  tff(c_2537, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_2505, c_10])).
% 4.77/1.79  tff(c_2591, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2534, c_2537, c_2511, c_74])).
% 4.77/1.79  tff(c_2657, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_2591])).
% 4.77/1.79  tff(c_3216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3212, c_2657])).
% 4.77/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.79  
% 4.77/1.79  Inference rules
% 4.77/1.79  ----------------------
% 4.77/1.79  #Ref     : 0
% 4.77/1.79  #Sup     : 650
% 4.77/1.79  #Fact    : 0
% 4.77/1.79  #Define  : 0
% 4.77/1.79  #Split   : 8
% 4.77/1.79  #Chain   : 0
% 4.77/1.79  #Close   : 0
% 4.77/1.79  
% 4.77/1.79  Ordering : KBO
% 4.77/1.79  
% 4.77/1.79  Simplification rules
% 4.77/1.79  ----------------------
% 4.77/1.79  #Subsume      : 174
% 4.77/1.79  #Demod        : 476
% 4.77/1.79  #Tautology    : 247
% 4.77/1.79  #SimpNegUnit  : 4
% 4.77/1.79  #BackRed      : 32
% 4.77/1.79  
% 4.77/1.79  #Partial instantiations: 0
% 4.77/1.79  #Strategies tried      : 1
% 4.77/1.79  
% 4.77/1.79  Timing (in seconds)
% 4.77/1.79  ----------------------
% 4.77/1.79  Preprocessing        : 0.33
% 4.77/1.79  Parsing              : 0.18
% 4.77/1.79  CNF conversion       : 0.02
% 4.77/1.79  Main loop            : 0.71
% 4.77/1.79  Inferencing          : 0.26
% 4.77/1.79  Reduction            : 0.23
% 4.77/1.79  Demodulation         : 0.16
% 4.77/1.79  BG Simplification    : 0.03
% 4.77/1.79  Subsumption          : 0.13
% 4.77/1.79  Abstraction          : 0.03
% 4.77/1.79  MUC search           : 0.00
% 4.77/1.79  Cooper               : 0.00
% 4.77/1.79  Total                : 1.09
% 4.77/1.79  Index Insertion      : 0.00
% 4.77/1.79  Index Deletion       : 0.00
% 4.77/1.79  Index Matching       : 0.00
% 4.77/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
