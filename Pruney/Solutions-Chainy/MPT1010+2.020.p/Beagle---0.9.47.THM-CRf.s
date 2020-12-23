%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 116 expanded)
%              Number of leaves         :   47 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 221 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_249,plain,(
    ! [C_123,B_124,A_125] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_258,plain,(
    v5_relat_1('#skF_10',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_249])).

tff(c_82,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_155,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_164,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_84,c_155])).

tff(c_88,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_86,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_302,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_311,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_84,c_302])).

tff(c_846,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_853,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_846])).

tff(c_857,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_311,c_853])).

tff(c_858,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_382,plain,(
    ! [A_161,D_162] :
      ( r2_hidden(k1_funct_1(A_161,D_162),k2_relat_1(A_161))
      | ~ r2_hidden(D_162,k1_relat_1(A_161))
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_295,plain,(
    ! [A_132,C_133,B_134] :
      ( m1_subset_1(A_132,C_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(C_133))
      | ~ r2_hidden(A_132,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_300,plain,(
    ! [A_132,B_15,A_14] :
      ( m1_subset_1(A_132,B_15)
      | ~ r2_hidden(A_132,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_32,c_295])).

tff(c_6202,plain,(
    ! [A_19576,D_19577,B_19578] :
      ( m1_subset_1(k1_funct_1(A_19576,D_19577),B_19578)
      | ~ r1_tarski(k2_relat_1(A_19576),B_19578)
      | ~ r2_hidden(D_19577,k1_relat_1(A_19576))
      | ~ v1_funct_1(A_19576)
      | ~ v1_relat_1(A_19576) ) ),
    inference(resolution,[status(thm)],[c_382,c_300])).

tff(c_6209,plain,(
    ! [B_19672,D_19673,A_19674] :
      ( m1_subset_1(k1_funct_1(B_19672,D_19673),A_19674)
      | ~ r2_hidden(D_19673,k1_relat_1(B_19672))
      | ~ v1_funct_1(B_19672)
      | ~ v5_relat_1(B_19672,A_19674)
      | ~ v1_relat_1(B_19672) ) ),
    inference(resolution,[status(thm)],[c_38,c_6202])).

tff(c_6228,plain,(
    ! [D_19673,A_19674] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_19673),A_19674)
      | ~ r2_hidden(D_19673,'#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_19674)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_6209])).

tff(c_6243,plain,(
    ! [D_19768,A_19769] :
      ( m1_subset_1(k1_funct_1('#skF_10',D_19768),A_19769)
      | ~ r2_hidden(D_19768,'#skF_7')
      | ~ v5_relat_1('#skF_10',A_19769) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_88,c_6228])).

tff(c_26,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_215,plain,(
    ! [D_115,B_116,A_117] :
      ( D_115 = B_116
      | D_115 = A_117
      | ~ r2_hidden(D_115,k2_tarski(A_117,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_235,plain,(
    ! [D_119,A_120] :
      ( D_119 = A_120
      | D_119 = A_120
      | ~ r2_hidden(D_119,k1_tarski(A_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_215])).

tff(c_239,plain,(
    ! [A_120,A_12] :
      ( A_120 = A_12
      | v1_xboole_0(k1_tarski(A_120))
      | ~ m1_subset_1(A_12,k1_tarski(A_120)) ) ),
    inference(resolution,[status(thm)],[c_28,c_235])).

tff(c_245,plain,(
    ! [A_120,A_12] :
      ( A_120 = A_12
      | ~ m1_subset_1(A_12,k1_tarski(A_120)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_239])).

tff(c_6337,plain,(
    ! [D_19956,A_19957] :
      ( k1_funct_1('#skF_10',D_19956) = A_19957
      | ~ r2_hidden(D_19956,'#skF_7')
      | ~ v5_relat_1('#skF_10',k1_tarski(A_19957)) ) ),
    inference(resolution,[status(thm)],[c_6243,c_245])).

tff(c_6379,plain,(
    ! [A_20051] :
      ( k1_funct_1('#skF_10','#skF_9') = A_20051
      | ~ v5_relat_1('#skF_10',k1_tarski(A_20051)) ) ),
    inference(resolution,[status(thm)],[c_82,c_6337])).

tff(c_6388,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_258,c_6379])).

tff(c_6392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6388])).

tff(c_6393,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_93,plain,(
    ! [A_81] : k2_tarski(A_81,A_81) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [D_7,B_3] : r2_hidden(D_7,k2_tarski(D_7,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    ! [A_81] : r2_hidden(A_81,k1_tarski(A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_110,plain,(
    ! [B_83,A_84] :
      ( ~ r1_tarski(B_83,A_84)
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    ! [A_81] : ~ r1_tarski(k1_tarski(A_81),A_81) ),
    inference(resolution,[status(thm)],[c_99,c_110])).

tff(c_6414,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6393,c_123])).

tff(c_6426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.47  
% 7.10/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 7.10/2.47  
% 7.10/2.47  %Foreground sorts:
% 7.10/2.47  
% 7.10/2.47  
% 7.10/2.47  %Background operators:
% 7.10/2.47  
% 7.10/2.47  
% 7.10/2.47  %Foreground operators:
% 7.10/2.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.10/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.10/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.10/2.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.10/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.10/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.10/2.47  tff('#skF_7', type, '#skF_7': $i).
% 7.10/2.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.10/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.47  tff('#skF_10', type, '#skF_10': $i).
% 7.10/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.10/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.10/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.10/2.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.10/2.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.10/2.47  tff('#skF_9', type, '#skF_9': $i).
% 7.10/2.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.10/2.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.10/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.10/2.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.10/2.47  tff('#skF_8', type, '#skF_8': $i).
% 7.10/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.10/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.10/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.10/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.10/2.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.10/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.10/2.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.10/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.10/2.47  
% 7.10/2.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.10/2.48  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 7.10/2.48  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.10/2.48  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.10/2.48  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.10/2.48  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.10/2.48  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.10/2.48  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.10/2.48  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.10/2.48  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.10/2.48  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.10/2.48  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.10/2.48  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.10/2.48  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.10/2.48  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.10/2.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.10/2.48  tff(c_80, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.10/2.48  tff(c_84, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.10/2.48  tff(c_249, plain, (![C_123, B_124, A_125]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.10/2.48  tff(c_258, plain, (v5_relat_1('#skF_10', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_84, c_249])).
% 7.10/2.48  tff(c_82, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.10/2.48  tff(c_155, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.10/2.48  tff(c_164, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_84, c_155])).
% 7.10/2.48  tff(c_88, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.10/2.48  tff(c_86, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.10/2.48  tff(c_302, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.10/2.48  tff(c_311, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_84, c_302])).
% 7.10/2.48  tff(c_846, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.10/2.48  tff(c_853, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_84, c_846])).
% 7.10/2.48  tff(c_857, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_311, c_853])).
% 7.10/2.48  tff(c_858, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_857])).
% 7.10/2.48  tff(c_38, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.10/2.48  tff(c_382, plain, (![A_161, D_162]: (r2_hidden(k1_funct_1(A_161, D_162), k2_relat_1(A_161)) | ~r2_hidden(D_162, k1_relat_1(A_161)) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.10/2.48  tff(c_32, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.10/2.48  tff(c_295, plain, (![A_132, C_133, B_134]: (m1_subset_1(A_132, C_133) | ~m1_subset_1(B_134, k1_zfmisc_1(C_133)) | ~r2_hidden(A_132, B_134))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.10/2.48  tff(c_300, plain, (![A_132, B_15, A_14]: (m1_subset_1(A_132, B_15) | ~r2_hidden(A_132, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_32, c_295])).
% 7.10/2.48  tff(c_6202, plain, (![A_19576, D_19577, B_19578]: (m1_subset_1(k1_funct_1(A_19576, D_19577), B_19578) | ~r1_tarski(k2_relat_1(A_19576), B_19578) | ~r2_hidden(D_19577, k1_relat_1(A_19576)) | ~v1_funct_1(A_19576) | ~v1_relat_1(A_19576))), inference(resolution, [status(thm)], [c_382, c_300])).
% 7.10/2.48  tff(c_6209, plain, (![B_19672, D_19673, A_19674]: (m1_subset_1(k1_funct_1(B_19672, D_19673), A_19674) | ~r2_hidden(D_19673, k1_relat_1(B_19672)) | ~v1_funct_1(B_19672) | ~v5_relat_1(B_19672, A_19674) | ~v1_relat_1(B_19672))), inference(resolution, [status(thm)], [c_38, c_6202])).
% 7.10/2.48  tff(c_6228, plain, (![D_19673, A_19674]: (m1_subset_1(k1_funct_1('#skF_10', D_19673), A_19674) | ~r2_hidden(D_19673, '#skF_7') | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_19674) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_858, c_6209])).
% 7.10/2.48  tff(c_6243, plain, (![D_19768, A_19769]: (m1_subset_1(k1_funct_1('#skF_10', D_19768), A_19769) | ~r2_hidden(D_19768, '#skF_7') | ~v5_relat_1('#skF_10', A_19769))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_88, c_6228])).
% 7.10/2.48  tff(c_26, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.10/2.48  tff(c_28, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.10/2.48  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.10/2.48  tff(c_215, plain, (![D_115, B_116, A_117]: (D_115=B_116 | D_115=A_117 | ~r2_hidden(D_115, k2_tarski(A_117, B_116)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.10/2.48  tff(c_235, plain, (![D_119, A_120]: (D_119=A_120 | D_119=A_120 | ~r2_hidden(D_119, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_215])).
% 7.10/2.48  tff(c_239, plain, (![A_120, A_12]: (A_120=A_12 | v1_xboole_0(k1_tarski(A_120)) | ~m1_subset_1(A_12, k1_tarski(A_120)))), inference(resolution, [status(thm)], [c_28, c_235])).
% 7.10/2.48  tff(c_245, plain, (![A_120, A_12]: (A_120=A_12 | ~m1_subset_1(A_12, k1_tarski(A_120)))), inference(negUnitSimplification, [status(thm)], [c_26, c_239])).
% 7.10/2.48  tff(c_6337, plain, (![D_19956, A_19957]: (k1_funct_1('#skF_10', D_19956)=A_19957 | ~r2_hidden(D_19956, '#skF_7') | ~v5_relat_1('#skF_10', k1_tarski(A_19957)))), inference(resolution, [status(thm)], [c_6243, c_245])).
% 7.10/2.48  tff(c_6379, plain, (![A_20051]: (k1_funct_1('#skF_10', '#skF_9')=A_20051 | ~v5_relat_1('#skF_10', k1_tarski(A_20051)))), inference(resolution, [status(thm)], [c_82, c_6337])).
% 7.10/2.48  tff(c_6388, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_258, c_6379])).
% 7.10/2.48  tff(c_6392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_6388])).
% 7.10/2.48  tff(c_6393, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_857])).
% 7.10/2.48  tff(c_93, plain, (![A_81]: (k2_tarski(A_81, A_81)=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.10/2.48  tff(c_8, plain, (![D_7, B_3]: (r2_hidden(D_7, k2_tarski(D_7, B_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.10/2.48  tff(c_99, plain, (![A_81]: (r2_hidden(A_81, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 7.10/2.48  tff(c_110, plain, (![B_83, A_84]: (~r1_tarski(B_83, A_84) | ~r2_hidden(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.10/2.48  tff(c_123, plain, (![A_81]: (~r1_tarski(k1_tarski(A_81), A_81))), inference(resolution, [status(thm)], [c_99, c_110])).
% 7.10/2.48  tff(c_6414, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6393, c_123])).
% 7.10/2.48  tff(c_6426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6414])).
% 7.10/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.48  
% 7.10/2.48  Inference rules
% 7.10/2.48  ----------------------
% 7.10/2.48  #Ref     : 0
% 7.10/2.48  #Sup     : 759
% 7.10/2.48  #Fact    : 8
% 7.10/2.48  #Define  : 0
% 7.10/2.48  #Split   : 26
% 7.10/2.48  #Chain   : 0
% 7.10/2.48  #Close   : 0
% 7.10/2.48  
% 7.10/2.48  Ordering : KBO
% 7.10/2.48  
% 7.10/2.48  Simplification rules
% 7.10/2.48  ----------------------
% 7.10/2.48  #Subsume      : 141
% 7.10/2.48  #Demod        : 237
% 7.10/2.48  #Tautology    : 137
% 7.10/2.48  #SimpNegUnit  : 7
% 7.10/2.48  #BackRed      : 16
% 7.10/2.49  
% 7.10/2.49  #Partial instantiations: 12720
% 7.10/2.49  #Strategies tried      : 1
% 7.10/2.49  
% 7.10/2.49  Timing (in seconds)
% 7.10/2.49  ----------------------
% 7.10/2.49  Preprocessing        : 0.37
% 7.10/2.49  Parsing              : 0.18
% 7.10/2.49  CNF conversion       : 0.03
% 7.10/2.49  Main loop            : 1.34
% 7.10/2.49  Inferencing          : 0.63
% 7.10/2.49  Reduction            : 0.36
% 7.10/2.49  Demodulation         : 0.26
% 7.10/2.49  BG Simplification    : 0.06
% 7.10/2.49  Subsumption          : 0.19
% 7.10/2.49  Abstraction          : 0.06
% 7.10/2.49  MUC search           : 0.00
% 7.10/2.49  Cooper               : 0.00
% 7.10/2.49  Total                : 1.75
% 7.10/2.49  Index Insertion      : 0.00
% 7.10/2.49  Index Deletion       : 0.00
% 7.10/2.49  Index Matching       : 0.00
% 7.10/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
