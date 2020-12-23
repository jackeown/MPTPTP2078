%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 267 expanded)
%              Number of leaves         :   28 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 599 expanded)
%              Number of equality atoms :   17 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(B_25,A_24)
      | ~ v1_xboole_0(B_25)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_107,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(B_45,A_46)
      | ~ v1_xboole_0(B_45)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_4'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ! [C_35] :
      ( ~ r2_hidden(C_35,'#skF_8')
      | ~ m1_subset_1(C_35,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8'),'#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_72,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_68])).

tff(c_119,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_8'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_107,c_72])).

tff(c_120,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_173,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_121,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_8')
      | ~ m1_subset_1(C_28,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_136,plain,(
    ! [B_47] :
      ( ~ m1_subset_1(B_47,'#skF_7')
      | ~ m1_subset_1(B_47,'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_121,c_42])).

tff(c_217,plain,(
    ! [B_60] :
      ( ~ m1_subset_1(B_60,'#skF_7')
      | ~ m1_subset_1(B_60,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_221,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_173,c_217])).

tff(c_228,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_221])).

tff(c_233,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_234,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_125,plain,(
    ! [B_47,A_19] :
      ( r1_tarski(B_47,A_19)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_121,c_20])).

tff(c_138,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_125])).

tff(c_147,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_138])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_151,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_147,c_18])).

tff(c_235,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_242,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_8','#skF_7')
      | ~ r2_hidden(C_63,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_235])).

tff(c_284,plain,(
    ~ r1_xboole_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_259,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),B_65)
      | r1_xboole_0(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(B_25,A_24)
      | ~ r2_hidden(B_25,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1369,plain,(
    ! [A_153,B_154] :
      ( m1_subset_1('#skF_2'(A_153,B_154),B_154)
      | v1_xboole_0(B_154)
      | r1_xboole_0(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_259,c_32])).

tff(c_175,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [B_54] :
      ( ~ m1_subset_1('#skF_2'('#skF_8',B_54),'#skF_7')
      | r1_xboole_0('#skF_8',B_54) ) ),
    inference(resolution,[status(thm)],[c_175,c_42])).

tff(c_1373,plain,
    ( v1_xboole_0('#skF_7')
    | r1_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_1369,c_192])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_120,c_284,c_1373])).

tff(c_1391,plain,(
    ! [C_155] : ~ r2_hidden(C_155,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_1407,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_1391])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_1407])).

tff(c_1422,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_49,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_4'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(resolution,[status(thm)],[c_49,c_2])).

tff(c_1425,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1422,c_53])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1425])).

tff(c_1431,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1435,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1431,c_53])).

tff(c_1438,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_44])).

tff(c_1437,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_4'(A_15),A_15)
      | A_15 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_16])).

tff(c_1581,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_2'(A_170,B_171),B_171)
      | r1_xboole_0(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1605,plain,(
    ! [B_172,A_173] :
      ( ~ v1_xboole_0(B_172)
      | r1_xboole_0(A_173,B_172) ) ),
    inference(resolution,[status(thm)],[c_1581,c_2])).

tff(c_1467,plain,(
    ! [B_158,A_159] :
      ( r2_hidden(B_158,A_159)
      | ~ m1_subset_1(B_158,A_159)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1471,plain,(
    ! [B_158,A_19] :
      ( r1_tarski(B_158,A_19)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1467,c_20])).

tff(c_1484,plain,(
    ! [B_160,A_161] :
      ( r1_tarski(B_160,A_161)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_161)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1471])).

tff(c_1493,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_1484])).

tff(c_1497,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1493,c_18])).

tff(c_1518,plain,(
    ! [A_164,B_165,C_166] :
      ( ~ r1_xboole_0(A_164,B_165)
      | ~ r2_hidden(C_166,k3_xboole_0(A_164,B_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1521,plain,(
    ! [C_166] :
      ( ~ r1_xboole_0('#skF_8','#skF_7')
      | ~ r2_hidden(C_166,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_1518])).

tff(c_1580,plain,(
    ~ r1_xboole_0('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_1608,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1605,c_1580])).

tff(c_1612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1608])).

tff(c_1615,plain,(
    ! [C_174] : ~ r2_hidden(C_174,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_1623,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1437,c_1615])).

tff(c_1634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1438,c_1623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.59  
% 3.16/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_5
% 3.16/1.59  
% 3.16/1.59  %Foreground sorts:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Background operators:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Foreground operators:
% 3.16/1.59  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.16/1.59  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.59  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.16/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.59  
% 3.16/1.61  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.16/1.61  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.16/1.61  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.16/1.61  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.16/1.61  tff(f_82, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.16/1.61  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.16/1.61  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.16/1.61  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.16/1.61  tff(c_44, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.16/1.61  tff(c_36, plain, (![B_25, A_24]: (m1_subset_1(B_25, A_24) | ~v1_xboole_0(B_25) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_107, plain, (![B_45, A_46]: (m1_subset_1(B_45, A_46) | ~v1_xboole_0(B_45) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_16, plain, (![A_15]: (r2_hidden('#skF_4'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.61  tff(c_60, plain, (![C_35]: (~r2_hidden(C_35, '#skF_8') | ~m1_subset_1(C_35, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.16/1.61  tff(c_68, plain, (~m1_subset_1('#skF_4'('#skF_8'), '#skF_7') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_16, c_60])).
% 3.16/1.61  tff(c_72, plain, (~m1_subset_1('#skF_4'('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_68])).
% 3.16/1.61  tff(c_119, plain, (~v1_xboole_0('#skF_4'('#skF_8')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_107, c_72])).
% 3.16/1.61  tff(c_120, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_119])).
% 3.16/1.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.61  tff(c_156, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_173, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_156])).
% 3.16/1.61  tff(c_121, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_42, plain, (![C_28]: (~r2_hidden(C_28, '#skF_8') | ~m1_subset_1(C_28, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.16/1.61  tff(c_136, plain, (![B_47]: (~m1_subset_1(B_47, '#skF_7') | ~m1_subset_1(B_47, '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_121, c_42])).
% 3.16/1.61  tff(c_217, plain, (![B_60]: (~m1_subset_1(B_60, '#skF_7') | ~m1_subset_1(B_60, '#skF_8'))), inference(splitLeft, [status(thm)], [c_136])).
% 3.16/1.61  tff(c_221, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_173, c_217])).
% 3.16/1.61  tff(c_228, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_120, c_221])).
% 3.16/1.61  tff(c_233, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_36, c_228])).
% 3.16/1.61  tff(c_234, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_233])).
% 3.16/1.61  tff(c_46, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.16/1.61  tff(c_40, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.16/1.61  tff(c_20, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.61  tff(c_125, plain, (![B_47, A_19]: (r1_tarski(B_47, A_19) | ~m1_subset_1(B_47, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_121, c_20])).
% 3.16/1.61  tff(c_138, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_40, c_125])).
% 3.16/1.61  tff(c_147, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_138])).
% 3.16/1.61  tff(c_18, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.61  tff(c_151, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_147, c_18])).
% 3.16/1.61  tff(c_235, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.61  tff(c_242, plain, (![C_63]: (~r1_xboole_0('#skF_8', '#skF_7') | ~r2_hidden(C_63, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_235])).
% 3.16/1.61  tff(c_284, plain, (~r1_xboole_0('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_242])).
% 3.16/1.61  tff(c_259, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), B_65) | r1_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.61  tff(c_32, plain, (![B_25, A_24]: (m1_subset_1(B_25, A_24) | ~r2_hidden(B_25, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_1369, plain, (![A_153, B_154]: (m1_subset_1('#skF_2'(A_153, B_154), B_154) | v1_xboole_0(B_154) | r1_xboole_0(A_153, B_154))), inference(resolution, [status(thm)], [c_259, c_32])).
% 3.16/1.61  tff(c_175, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.61  tff(c_192, plain, (![B_54]: (~m1_subset_1('#skF_2'('#skF_8', B_54), '#skF_7') | r1_xboole_0('#skF_8', B_54))), inference(resolution, [status(thm)], [c_175, c_42])).
% 3.16/1.61  tff(c_1373, plain, (v1_xboole_0('#skF_7') | r1_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_1369, c_192])).
% 3.16/1.61  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_120, c_284, c_1373])).
% 3.16/1.61  tff(c_1391, plain, (![C_155]: (~r2_hidden(C_155, '#skF_8'))), inference(splitRight, [status(thm)], [c_242])).
% 3.16/1.61  tff(c_1407, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_1391])).
% 3.16/1.61  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_1407])).
% 3.16/1.61  tff(c_1422, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_233])).
% 3.16/1.61  tff(c_49, plain, (![A_32]: (r2_hidden('#skF_4'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.61  tff(c_53, plain, (![A_32]: (~v1_xboole_0(A_32) | k1_xboole_0=A_32)), inference(resolution, [status(thm)], [c_49, c_2])).
% 3.16/1.61  tff(c_1425, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1422, c_53])).
% 3.16/1.61  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1425])).
% 3.16/1.61  tff(c_1431, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_119])).
% 3.16/1.61  tff(c_1435, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1431, c_53])).
% 3.16/1.61  tff(c_1438, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_44])).
% 3.16/1.61  tff(c_1437, plain, (![A_15]: (r2_hidden('#skF_4'(A_15), A_15) | A_15='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_16])).
% 3.16/1.61  tff(c_1581, plain, (![A_170, B_171]: (r2_hidden('#skF_2'(A_170, B_171), B_171) | r1_xboole_0(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.61  tff(c_1605, plain, (![B_172, A_173]: (~v1_xboole_0(B_172) | r1_xboole_0(A_173, B_172))), inference(resolution, [status(thm)], [c_1581, c_2])).
% 3.16/1.61  tff(c_1467, plain, (![B_158, A_159]: (r2_hidden(B_158, A_159) | ~m1_subset_1(B_158, A_159) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.61  tff(c_1471, plain, (![B_158, A_19]: (r1_tarski(B_158, A_19) | ~m1_subset_1(B_158, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1467, c_20])).
% 3.16/1.61  tff(c_1484, plain, (![B_160, A_161]: (r1_tarski(B_160, A_161) | ~m1_subset_1(B_160, k1_zfmisc_1(A_161)))), inference(negUnitSimplification, [status(thm)], [c_40, c_1471])).
% 3.16/1.61  tff(c_1493, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_46, c_1484])).
% 3.16/1.61  tff(c_1497, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_1493, c_18])).
% 3.16/1.61  tff(c_1518, plain, (![A_164, B_165, C_166]: (~r1_xboole_0(A_164, B_165) | ~r2_hidden(C_166, k3_xboole_0(A_164, B_165)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.61  tff(c_1521, plain, (![C_166]: (~r1_xboole_0('#skF_8', '#skF_7') | ~r2_hidden(C_166, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_1518])).
% 3.16/1.61  tff(c_1580, plain, (~r1_xboole_0('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_1521])).
% 3.16/1.61  tff(c_1608, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1605, c_1580])).
% 3.16/1.61  tff(c_1612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1608])).
% 3.16/1.61  tff(c_1615, plain, (![C_174]: (~r2_hidden(C_174, '#skF_8'))), inference(splitRight, [status(thm)], [c_1521])).
% 3.16/1.61  tff(c_1623, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_1437, c_1615])).
% 3.16/1.61  tff(c_1634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1438, c_1623])).
% 3.16/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.61  
% 3.16/1.61  Inference rules
% 3.16/1.61  ----------------------
% 3.16/1.61  #Ref     : 0
% 3.16/1.61  #Sup     : 338
% 3.16/1.61  #Fact    : 0
% 3.16/1.61  #Define  : 0
% 3.16/1.61  #Split   : 11
% 3.16/1.61  #Chain   : 0
% 3.16/1.61  #Close   : 0
% 3.16/1.61  
% 3.16/1.61  Ordering : KBO
% 3.16/1.61  
% 3.16/1.61  Simplification rules
% 3.16/1.61  ----------------------
% 3.16/1.61  #Subsume      : 104
% 3.16/1.61  #Demod        : 80
% 3.16/1.61  #Tautology    : 102
% 3.16/1.61  #SimpNegUnit  : 56
% 3.16/1.61  #BackRed      : 16
% 3.16/1.61  
% 3.16/1.61  #Partial instantiations: 0
% 3.16/1.61  #Strategies tried      : 1
% 3.16/1.61  
% 3.16/1.61  Timing (in seconds)
% 3.16/1.61  ----------------------
% 3.16/1.61  Preprocessing        : 0.34
% 3.16/1.61  Parsing              : 0.18
% 3.16/1.61  CNF conversion       : 0.03
% 3.16/1.61  Main loop            : 0.44
% 3.16/1.61  Inferencing          : 0.17
% 3.16/1.61  Reduction            : 0.12
% 3.16/1.61  Demodulation         : 0.07
% 3.16/1.61  BG Simplification    : 0.03
% 3.16/1.61  Subsumption          : 0.09
% 3.16/1.61  Abstraction          : 0.02
% 3.16/1.61  MUC search           : 0.00
% 3.16/1.61  Cooper               : 0.00
% 3.16/1.61  Total                : 0.82
% 3.16/1.61  Index Insertion      : 0.00
% 3.16/1.61  Index Deletion       : 0.00
% 3.16/1.61  Index Matching       : 0.00
% 3.16/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
