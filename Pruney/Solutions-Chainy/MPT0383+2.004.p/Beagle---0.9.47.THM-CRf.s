%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:07 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 218 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 495 expanded)
%              Number of equality atoms :   12 (  82 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_44,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    k2_xboole_0('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_58])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_128,plain,(
    ! [D_10] :
      ( ~ r2_hidden(D_10,'#skF_8')
      | r2_hidden(D_10,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_46,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_47])).

tff(c_68,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,
    ( m1_subset_1('#skF_9','#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_78,plain,(
    m1_subset_1('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_74])).

tff(c_279,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_tarski('#skF_4'(A_90,B_91,C_92),'#skF_5'(A_90,B_91,C_92)) = A_90
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [B_59,D_60,A_61,C_62] :
      ( r2_hidden(B_59,D_60)
      | ~ r2_hidden(k4_tarski(A_61,B_59),k2_zfmisc_1(C_62,D_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [B_59,A_61] :
      ( r2_hidden(B_59,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_61,B_59),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_142])).

tff(c_390,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_5'(A_113,B_114,C_115),'#skF_7')
      | ~ r2_hidden(A_113,'#skF_8')
      | ~ r2_hidden(A_113,k2_zfmisc_1(B_114,C_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_150])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_398,plain,(
    ! [A_113,B_114,C_115] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_113,'#skF_8')
      | ~ r2_hidden(A_113,k2_zfmisc_1(B_114,C_115)) ) ),
    inference(resolution,[status(thm)],[c_390,c_2])).

tff(c_416,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_64,B_63),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_142])).

tff(c_155,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ m1_subset_1(k4_tarski(A_64,B_63),'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_158,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,'#skF_7')
      | ~ m1_subset_1(k4_tarski(A_64,B_63),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_155])).

tff(c_434,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_5'(A_123,B_124,C_125),'#skF_7')
      | ~ m1_subset_1(A_123,'#skF_8')
      | ~ r2_hidden(A_123,k2_zfmisc_1(B_124,C_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_158])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ r2_hidden(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_437,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_subset_1('#skF_5'(A_123,B_124,C_125),'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_123,'#skF_8')
      | ~ r2_hidden(A_123,k2_zfmisc_1(B_124,C_125)) ) ),
    inference(resolution,[status(thm)],[c_434,c_34])).

tff(c_473,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_5'(A_130,B_131,C_132),'#skF_7')
      | ~ m1_subset_1(A_130,'#skF_8')
      | ~ r2_hidden(A_130,k2_zfmisc_1(B_131,C_132)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_437])).

tff(c_489,plain,(
    ! [D_10] :
      ( m1_subset_1('#skF_5'(D_10,'#skF_6','#skF_7'),'#skF_7')
      | ~ m1_subset_1(D_10,'#skF_8')
      | ~ r2_hidden(D_10,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_473])).

tff(c_164,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1(C_68,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_172,plain,(
    ! [A_67,B_69] :
      ( r2_hidden(A_67,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_67,B_69),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_164])).

tff(c_380,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden('#skF_4'(A_110,B_111,C_112),'#skF_6')
      | ~ r2_hidden(A_110,'#skF_8')
      | ~ r2_hidden(A_110,k2_zfmisc_1(B_111,C_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_172])).

tff(c_388,plain,(
    ! [A_110,B_111,C_112] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_110,'#skF_8')
      | ~ r2_hidden(A_110,k2_zfmisc_1(B_111,C_112)) ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_389,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_174,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_71,B_72),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_164])).

tff(c_177,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,'#skF_6')
      | ~ m1_subset_1(k4_tarski(A_71,B_72),'#skF_8')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_180,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,'#skF_6')
      | ~ m1_subset_1(k4_tarski(A_71,B_72),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_177])).

tff(c_417,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_4'(A_119,B_120,C_121),'#skF_6')
      | ~ m1_subset_1(A_119,'#skF_8')
      | ~ r2_hidden(A_119,k2_zfmisc_1(B_120,C_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_180])).

tff(c_420,plain,(
    ! [A_119,B_120,C_121] :
      ( m1_subset_1('#skF_4'(A_119,B_120,C_121),'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_119,'#skF_8')
      | ~ r2_hidden(A_119,k2_zfmisc_1(B_120,C_121)) ) ),
    inference(resolution,[status(thm)],[c_417,c_34])).

tff(c_445,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1('#skF_4'(A_126,B_127,C_128),'#skF_6')
      | ~ m1_subset_1(A_126,'#skF_8')
      | ~ r2_hidden(A_126,k2_zfmisc_1(B_127,C_128)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_420])).

tff(c_464,plain,(
    ! [D_129] :
      ( m1_subset_1('#skF_4'(D_129,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_subset_1(D_129,'#skF_8')
      | ~ r2_hidden(D_129,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_445])).

tff(c_42,plain,(
    ! [E_27,F_29] :
      ( k4_tarski(E_27,F_29) != '#skF_9'
      | ~ m1_subset_1(F_29,'#skF_7')
      | ~ m1_subset_1(E_27,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_341,plain,(
    ! [A_103,B_104,C_105] :
      ( A_103 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(A_103,B_104,C_105),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_103,B_104,C_105),'#skF_6')
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_42])).

tff(c_357,plain,(
    ! [D_10] :
      ( D_10 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(D_10,'#skF_6','#skF_7'),'#skF_7')
      | ~ m1_subset_1('#skF_4'(D_10,'#skF_6','#skF_7'),'#skF_6')
      | ~ r2_hidden(D_10,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_128,c_341])).

tff(c_515,plain,(
    ! [D_137] :
      ( D_137 != '#skF_9'
      | ~ m1_subset_1('#skF_5'(D_137,'#skF_6','#skF_7'),'#skF_7')
      | ~ m1_subset_1(D_137,'#skF_8')
      | ~ r2_hidden(D_137,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_464,c_357])).

tff(c_525,plain,(
    ! [D_138] :
      ( D_138 != '#skF_9'
      | ~ m1_subset_1(D_138,'#skF_8')
      | ~ r2_hidden(D_138,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_489,c_515])).

tff(c_536,plain,(
    ~ m1_subset_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_525])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_536])).

tff(c_554,plain,(
    ! [A_140,B_141,C_142] :
      ( ~ r2_hidden(A_140,'#skF_8')
      | ~ r2_hidden(A_140,k2_zfmisc_1(B_141,C_142)) ) ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_570,plain,(
    ! [D_10] : ~ r2_hidden(D_10,'#skF_8') ),
    inference(resolution,[status(thm)],[c_128,c_554])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_46])).

tff(c_577,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r2_hidden(A_143,'#skF_8')
      | ~ r2_hidden(A_143,k2_zfmisc_1(B_144,C_145)) ) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_593,plain,(
    ! [D_10] : ~ r2_hidden(D_10,'#skF_8') ),
    inference(resolution,[status(thm)],[c_128,c_577])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.80/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.80/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.80/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.80/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.43  
% 2.80/1.44  tff(f_85, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_subset_1)).
% 2.80/1.44  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.80/1.44  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.80/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.80/1.44  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.80/1.44  tff(f_51, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.80/1.44  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.80/1.44  tff(c_44, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.44  tff(c_58, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.44  tff(c_62, plain, (k2_xboole_0('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_58])).
% 2.80/1.44  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.80/1.44  tff(c_128, plain, (![D_10]: (~r2_hidden(D_10, '#skF_8') | r2_hidden(D_10, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_10])).
% 2.80/1.44  tff(c_46, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.44  tff(c_47, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_51, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_47])).
% 2.80/1.44  tff(c_68, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.44  tff(c_74, plain, (m1_subset_1('#skF_9', '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_46, c_68])).
% 2.80/1.44  tff(c_78, plain, (m1_subset_1('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_51, c_74])).
% 2.80/1.44  tff(c_279, plain, (![A_90, B_91, C_92]: (k4_tarski('#skF_4'(A_90, B_91, C_92), '#skF_5'(A_90, B_91, C_92))=A_90 | ~r2_hidden(A_90, k2_zfmisc_1(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.44  tff(c_142, plain, (![B_59, D_60, A_61, C_62]: (r2_hidden(B_59, D_60) | ~r2_hidden(k4_tarski(A_61, B_59), k2_zfmisc_1(C_62, D_60)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.44  tff(c_150, plain, (![B_59, A_61]: (r2_hidden(B_59, '#skF_7') | ~r2_hidden(k4_tarski(A_61, B_59), '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_142])).
% 2.80/1.44  tff(c_390, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_5'(A_113, B_114, C_115), '#skF_7') | ~r2_hidden(A_113, '#skF_8') | ~r2_hidden(A_113, k2_zfmisc_1(B_114, C_115)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_150])).
% 2.80/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_398, plain, (![A_113, B_114, C_115]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_113, '#skF_8') | ~r2_hidden(A_113, k2_zfmisc_1(B_114, C_115)))), inference(resolution, [status(thm)], [c_390, c_2])).
% 2.80/1.44  tff(c_416, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_398])).
% 2.80/1.44  tff(c_36, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.44  tff(c_152, plain, (![B_63, A_64]: (r2_hidden(B_63, '#skF_7') | ~r2_hidden(k4_tarski(A_64, B_63), '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_142])).
% 2.80/1.44  tff(c_155, plain, (![B_63, A_64]: (r2_hidden(B_63, '#skF_7') | ~m1_subset_1(k4_tarski(A_64, B_63), '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_152])).
% 2.80/1.44  tff(c_158, plain, (![B_63, A_64]: (r2_hidden(B_63, '#skF_7') | ~m1_subset_1(k4_tarski(A_64, B_63), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_51, c_155])).
% 2.80/1.44  tff(c_434, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_5'(A_123, B_124, C_125), '#skF_7') | ~m1_subset_1(A_123, '#skF_8') | ~r2_hidden(A_123, k2_zfmisc_1(B_124, C_125)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_158])).
% 2.80/1.44  tff(c_34, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~r2_hidden(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.44  tff(c_437, plain, (![A_123, B_124, C_125]: (m1_subset_1('#skF_5'(A_123, B_124, C_125), '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_123, '#skF_8') | ~r2_hidden(A_123, k2_zfmisc_1(B_124, C_125)))), inference(resolution, [status(thm)], [c_434, c_34])).
% 2.80/1.44  tff(c_473, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_5'(A_130, B_131, C_132), '#skF_7') | ~m1_subset_1(A_130, '#skF_8') | ~r2_hidden(A_130, k2_zfmisc_1(B_131, C_132)))), inference(negUnitSimplification, [status(thm)], [c_416, c_437])).
% 2.80/1.44  tff(c_489, plain, (![D_10]: (m1_subset_1('#skF_5'(D_10, '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1(D_10, '#skF_8') | ~r2_hidden(D_10, '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_473])).
% 2.80/1.44  tff(c_164, plain, (![A_67, C_68, B_69, D_70]: (r2_hidden(A_67, C_68) | ~r2_hidden(k4_tarski(A_67, B_69), k2_zfmisc_1(C_68, D_70)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.44  tff(c_172, plain, (![A_67, B_69]: (r2_hidden(A_67, '#skF_6') | ~r2_hidden(k4_tarski(A_67, B_69), '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_164])).
% 2.80/1.44  tff(c_380, plain, (![A_110, B_111, C_112]: (r2_hidden('#skF_4'(A_110, B_111, C_112), '#skF_6') | ~r2_hidden(A_110, '#skF_8') | ~r2_hidden(A_110, k2_zfmisc_1(B_111, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_172])).
% 2.80/1.44  tff(c_388, plain, (![A_110, B_111, C_112]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_110, '#skF_8') | ~r2_hidden(A_110, k2_zfmisc_1(B_111, C_112)))), inference(resolution, [status(thm)], [c_380, c_2])).
% 2.80/1.44  tff(c_389, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_388])).
% 2.80/1.44  tff(c_174, plain, (![A_71, B_72]: (r2_hidden(A_71, '#skF_6') | ~r2_hidden(k4_tarski(A_71, B_72), '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_164])).
% 2.80/1.44  tff(c_177, plain, (![A_71, B_72]: (r2_hidden(A_71, '#skF_6') | ~m1_subset_1(k4_tarski(A_71, B_72), '#skF_8') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_174])).
% 2.80/1.44  tff(c_180, plain, (![A_71, B_72]: (r2_hidden(A_71, '#skF_6') | ~m1_subset_1(k4_tarski(A_71, B_72), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_51, c_177])).
% 2.80/1.44  tff(c_417, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_4'(A_119, B_120, C_121), '#skF_6') | ~m1_subset_1(A_119, '#skF_8') | ~r2_hidden(A_119, k2_zfmisc_1(B_120, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_180])).
% 2.80/1.44  tff(c_420, plain, (![A_119, B_120, C_121]: (m1_subset_1('#skF_4'(A_119, B_120, C_121), '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_119, '#skF_8') | ~r2_hidden(A_119, k2_zfmisc_1(B_120, C_121)))), inference(resolution, [status(thm)], [c_417, c_34])).
% 2.80/1.44  tff(c_445, plain, (![A_126, B_127, C_128]: (m1_subset_1('#skF_4'(A_126, B_127, C_128), '#skF_6') | ~m1_subset_1(A_126, '#skF_8') | ~r2_hidden(A_126, k2_zfmisc_1(B_127, C_128)))), inference(negUnitSimplification, [status(thm)], [c_389, c_420])).
% 2.80/1.44  tff(c_464, plain, (![D_129]: (m1_subset_1('#skF_4'(D_129, '#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1(D_129, '#skF_8') | ~r2_hidden(D_129, '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_445])).
% 2.80/1.44  tff(c_42, plain, (![E_27, F_29]: (k4_tarski(E_27, F_29)!='#skF_9' | ~m1_subset_1(F_29, '#skF_7') | ~m1_subset_1(E_27, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.44  tff(c_341, plain, (![A_103, B_104, C_105]: (A_103!='#skF_9' | ~m1_subset_1('#skF_5'(A_103, B_104, C_105), '#skF_7') | ~m1_subset_1('#skF_4'(A_103, B_104, C_105), '#skF_6') | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_42])).
% 2.80/1.44  tff(c_357, plain, (![D_10]: (D_10!='#skF_9' | ~m1_subset_1('#skF_5'(D_10, '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_4'(D_10, '#skF_6', '#skF_7'), '#skF_6') | ~r2_hidden(D_10, '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_341])).
% 2.80/1.44  tff(c_515, plain, (![D_137]: (D_137!='#skF_9' | ~m1_subset_1('#skF_5'(D_137, '#skF_6', '#skF_7'), '#skF_7') | ~m1_subset_1(D_137, '#skF_8') | ~r2_hidden(D_137, '#skF_8'))), inference(resolution, [status(thm)], [c_464, c_357])).
% 2.80/1.44  tff(c_525, plain, (![D_138]: (D_138!='#skF_9' | ~m1_subset_1(D_138, '#skF_8') | ~r2_hidden(D_138, '#skF_8'))), inference(resolution, [status(thm)], [c_489, c_515])).
% 2.80/1.44  tff(c_536, plain, (~m1_subset_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_46, c_525])).
% 2.80/1.44  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_536])).
% 2.80/1.44  tff(c_554, plain, (![A_140, B_141, C_142]: (~r2_hidden(A_140, '#skF_8') | ~r2_hidden(A_140, k2_zfmisc_1(B_141, C_142)))), inference(splitRight, [status(thm)], [c_398])).
% 2.80/1.44  tff(c_570, plain, (![D_10]: (~r2_hidden(D_10, '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_554])).
% 2.80/1.44  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_46])).
% 2.80/1.44  tff(c_577, plain, (![A_143, B_144, C_145]: (~r2_hidden(A_143, '#skF_8') | ~r2_hidden(A_143, k2_zfmisc_1(B_144, C_145)))), inference(splitRight, [status(thm)], [c_388])).
% 2.80/1.44  tff(c_593, plain, (![D_10]: (~r2_hidden(D_10, '#skF_8'))), inference(resolution, [status(thm)], [c_128, c_577])).
% 2.80/1.44  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_593, c_46])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 0
% 2.80/1.44  #Sup     : 115
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 3
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 36
% 2.80/1.44  #Demod        : 3
% 2.80/1.44  #Tautology    : 20
% 2.80/1.44  #SimpNegUnit  : 18
% 2.80/1.44  #BackRed      : 2
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.45  Preprocessing        : 0.30
% 2.80/1.45  Parsing              : 0.16
% 2.80/1.45  CNF conversion       : 0.03
% 2.80/1.45  Main loop            : 0.38
% 2.80/1.45  Inferencing          : 0.16
% 2.80/1.45  Reduction            : 0.09
% 2.80/1.45  Demodulation         : 0.05
% 2.80/1.45  BG Simplification    : 0.02
% 2.80/1.45  Subsumption          : 0.09
% 2.80/1.45  Abstraction          : 0.02
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.72
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
