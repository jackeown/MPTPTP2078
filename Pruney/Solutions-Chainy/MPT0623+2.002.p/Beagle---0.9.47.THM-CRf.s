%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 157 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 342 expanded)
%              Number of equality atoms :   49 ( 168 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_372,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(k4_tarski('#skF_3'(A_96,B_97),'#skF_2'(A_96,B_97)),A_96)
      | r2_hidden('#skF_4'(A_96,B_97),B_97)
      | k2_relat_1(A_96) = B_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_61,C_62] :
      ( r2_hidden(k4_tarski('#skF_5'(A_61,k2_relat_1(A_61),C_62),C_62),A_61)
      | ~ r2_hidden(C_62,k2_relat_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_63,C_64] :
      ( ~ v1_xboole_0(A_63)
      | ~ r2_hidden(C_64,k2_relat_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_152,plain,(
    ! [C_64] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_138])).

tff(c_156,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_388,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_97),B_97)
      | k2_relat_1(k1_xboole_0) = B_97 ) ),
    inference(resolution,[status(thm)],[c_372,c_156])).

tff(c_403,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_97),B_97)
      | k1_xboole_0 = B_97 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_388])).

tff(c_38,plain,(
    ! [A_30,B_34] :
      ( k1_relat_1('#skF_6'(A_30,B_34)) = A_30
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_30,B_34] :
      ( v1_funct_1('#skF_6'(A_30,B_34))
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_30,B_34] :
      ( v1_relat_1('#skF_6'(A_30,B_34))
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_56,B_57] :
      ( k2_relat_1('#skF_6'(A_56,B_57)) = k1_tarski(B_57)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [C_37] :
      ( ~ r1_tarski(k2_relat_1(C_37),'#skF_7')
      | k1_relat_1(C_37) != '#skF_8'
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_206,plain,(
    ! [B_71,A_72] :
      ( ~ r1_tarski(k1_tarski(B_71),'#skF_7')
      | k1_relat_1('#skF_6'(A_72,B_71)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_72,B_71))
      | ~ v1_relat_1('#skF_6'(A_72,B_71))
      | k1_xboole_0 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_44])).

tff(c_320,plain,(
    ! [A_86,A_87] :
      ( k1_relat_1('#skF_6'(A_86,A_87)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_86,A_87))
      | ~ v1_relat_1('#skF_6'(A_86,A_87))
      | k1_xboole_0 = A_86
      | ~ r2_hidden(A_87,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_482,plain,(
    ! [A_101,B_102] :
      ( k1_relat_1('#skF_6'(A_101,B_102)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_101,B_102))
      | ~ r2_hidden(B_102,'#skF_7')
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_42,c_320])).

tff(c_1846,plain,(
    ! [A_135,B_136] :
      ( k1_relat_1('#skF_6'(A_135,B_136)) != '#skF_8'
      | ~ r2_hidden(B_136,'#skF_7')
      | k1_xboole_0 = A_135 ) ),
    inference(resolution,[status(thm)],[c_40,c_482])).

tff(c_1849,plain,(
    ! [A_30,B_34] :
      ( A_30 != '#skF_8'
      | ~ r2_hidden(B_34,'#skF_7')
      | k1_xboole_0 = A_30
      | k1_xboole_0 = A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1846])).

tff(c_1851,plain,(
    ! [B_137] : ~ r2_hidden(B_137,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1849])).

tff(c_1859,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_403,c_1851])).

tff(c_1876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1859])).

tff(c_1878,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1849])).

tff(c_62,plain,(
    ! [A_40] :
      ( v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_57,plain,(
    ! [A_39] :
      ( v1_funct_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_61,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [C_41] :
      ( ~ r1_tarski(k2_relat_1(C_41),'#skF_7')
      | k1_relat_1(C_41) != '#skF_8'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_7')
    | k1_relat_1(k1_xboole_0) != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_67])).

tff(c_72,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_32,c_8,c_70])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_72])).

tff(c_1907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_74])).

tff(c_1908,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1913,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_6])).

tff(c_1939,plain,(
    ! [A_140] :
      ( v1_relat_1(A_140)
      | ~ v1_xboole_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1943,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1913,c_1939])).

tff(c_1944,plain,(
    ! [A_141] :
      ( v1_funct_1(A_141)
      | ~ v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1948,plain,(
    v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1913,c_1944])).

tff(c_1912,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1908,c_32])).

tff(c_1910,plain,(
    ! [A_5] : r1_tarski('#skF_8',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_8])).

tff(c_1911,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1908,c_30])).

tff(c_1909,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1918,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1909])).

tff(c_1929,plain,(
    ! [C_139] :
      ( ~ r1_tarski(k2_relat_1(C_139),'#skF_8')
      | k1_relat_1(C_139) != '#skF_8'
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_44])).

tff(c_1932,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1911,c_1929])).

tff(c_1934,plain,
    ( k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1932])).

tff(c_1967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1943,c_1948,c_1912,c_1934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.58  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 3.37/1.58  
% 3.37/1.58  %Foreground sorts:
% 3.37/1.58  
% 3.37/1.58  
% 3.37/1.58  %Background operators:
% 3.37/1.58  
% 3.37/1.58  
% 3.37/1.58  %Foreground operators:
% 3.37/1.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.37/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.37/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.37/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.37/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.37/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.37/1.58  
% 3.37/1.59  tff(f_90, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.37/1.59  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.37/1.59  tff(f_52, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.37/1.59  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.37/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.37/1.59  tff(f_72, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.37/1.59  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.37/1.59  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.37/1.59  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 3.37/1.59  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.37/1.59  tff(c_46, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.37/1.59  tff(c_56, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_46])).
% 3.37/1.59  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.37/1.59  tff(c_372, plain, (![A_96, B_97]: (r2_hidden(k4_tarski('#skF_3'(A_96, B_97), '#skF_2'(A_96, B_97)), A_96) | r2_hidden('#skF_4'(A_96, B_97), B_97) | k2_relat_1(A_96)=B_97)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.37/1.59  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.59  tff(c_122, plain, (![A_61, C_62]: (r2_hidden(k4_tarski('#skF_5'(A_61, k2_relat_1(A_61), C_62), C_62), A_61) | ~r2_hidden(C_62, k2_relat_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.37/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.59  tff(c_138, plain, (![A_63, C_64]: (~v1_xboole_0(A_63) | ~r2_hidden(C_64, k2_relat_1(A_63)))), inference(resolution, [status(thm)], [c_122, c_2])).
% 3.37/1.59  tff(c_152, plain, (![C_64]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_138])).
% 3.37/1.59  tff(c_156, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_152])).
% 3.37/1.59  tff(c_388, plain, (![B_97]: (r2_hidden('#skF_4'(k1_xboole_0, B_97), B_97) | k2_relat_1(k1_xboole_0)=B_97)), inference(resolution, [status(thm)], [c_372, c_156])).
% 3.37/1.59  tff(c_403, plain, (![B_97]: (r2_hidden('#skF_4'(k1_xboole_0, B_97), B_97) | k1_xboole_0=B_97)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_388])).
% 3.37/1.59  tff(c_38, plain, (![A_30, B_34]: (k1_relat_1('#skF_6'(A_30, B_34))=A_30 | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.59  tff(c_40, plain, (![A_30, B_34]: (v1_funct_1('#skF_6'(A_30, B_34)) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.59  tff(c_42, plain, (![A_30, B_34]: (v1_relat_1('#skF_6'(A_30, B_34)) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.59  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.59  tff(c_109, plain, (![A_56, B_57]: (k2_relat_1('#skF_6'(A_56, B_57))=k1_tarski(B_57) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.59  tff(c_44, plain, (![C_37]: (~r1_tarski(k2_relat_1(C_37), '#skF_7') | k1_relat_1(C_37)!='#skF_8' | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.37/1.59  tff(c_206, plain, (![B_71, A_72]: (~r1_tarski(k1_tarski(B_71), '#skF_7') | k1_relat_1('#skF_6'(A_72, B_71))!='#skF_8' | ~v1_funct_1('#skF_6'(A_72, B_71)) | ~v1_relat_1('#skF_6'(A_72, B_71)) | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_109, c_44])).
% 3.37/1.59  tff(c_320, plain, (![A_86, A_87]: (k1_relat_1('#skF_6'(A_86, A_87))!='#skF_8' | ~v1_funct_1('#skF_6'(A_86, A_87)) | ~v1_relat_1('#skF_6'(A_86, A_87)) | k1_xboole_0=A_86 | ~r2_hidden(A_87, '#skF_7'))), inference(resolution, [status(thm)], [c_14, c_206])).
% 3.37/1.59  tff(c_482, plain, (![A_101, B_102]: (k1_relat_1('#skF_6'(A_101, B_102))!='#skF_8' | ~v1_funct_1('#skF_6'(A_101, B_102)) | ~r2_hidden(B_102, '#skF_7') | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_42, c_320])).
% 3.37/1.59  tff(c_1846, plain, (![A_135, B_136]: (k1_relat_1('#skF_6'(A_135, B_136))!='#skF_8' | ~r2_hidden(B_136, '#skF_7') | k1_xboole_0=A_135)), inference(resolution, [status(thm)], [c_40, c_482])).
% 3.37/1.59  tff(c_1849, plain, (![A_30, B_34]: (A_30!='#skF_8' | ~r2_hidden(B_34, '#skF_7') | k1_xboole_0=A_30 | k1_xboole_0=A_30)), inference(superposition, [status(thm), theory('equality')], [c_38, c_1846])).
% 3.37/1.59  tff(c_1851, plain, (![B_137]: (~r2_hidden(B_137, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1849])).
% 3.37/1.59  tff(c_1859, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_403, c_1851])).
% 3.37/1.59  tff(c_1876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1859])).
% 3.37/1.59  tff(c_1878, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1849])).
% 3.37/1.59  tff(c_62, plain, (![A_40]: (v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.37/1.59  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_62])).
% 3.37/1.59  tff(c_57, plain, (![A_39]: (v1_funct_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.37/1.59  tff(c_61, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_57])).
% 3.37/1.59  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.37/1.59  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.59  tff(c_67, plain, (![C_41]: (~r1_tarski(k2_relat_1(C_41), '#skF_7') | k1_relat_1(C_41)!='#skF_8' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.37/1.59  tff(c_70, plain, (~r1_tarski(k1_xboole_0, '#skF_7') | k1_relat_1(k1_xboole_0)!='#skF_8' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_67])).
% 3.37/1.59  tff(c_72, plain, (k1_xboole_0!='#skF_8' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_32, c_8, c_70])).
% 3.37/1.59  tff(c_74, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_72])).
% 3.37/1.59  tff(c_1907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1878, c_74])).
% 3.37/1.59  tff(c_1908, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_46])).
% 3.37/1.59  tff(c_1913, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_6])).
% 3.37/1.59  tff(c_1939, plain, (![A_140]: (v1_relat_1(A_140) | ~v1_xboole_0(A_140))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.37/1.59  tff(c_1943, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1913, c_1939])).
% 3.37/1.59  tff(c_1944, plain, (![A_141]: (v1_funct_1(A_141) | ~v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.37/1.59  tff(c_1948, plain, (v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1913, c_1944])).
% 3.37/1.59  tff(c_1912, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1908, c_32])).
% 3.37/1.59  tff(c_1910, plain, (![A_5]: (r1_tarski('#skF_8', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_8])).
% 3.37/1.59  tff(c_1911, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1908, c_30])).
% 3.37/1.59  tff(c_1909, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 3.37/1.59  tff(c_1918, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1909])).
% 3.37/1.59  tff(c_1929, plain, (![C_139]: (~r1_tarski(k2_relat_1(C_139), '#skF_8') | k1_relat_1(C_139)!='#skF_8' | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_44])).
% 3.37/1.59  tff(c_1932, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1911, c_1929])).
% 3.37/1.59  tff(c_1934, plain, (k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1932])).
% 3.37/1.59  tff(c_1967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1943, c_1948, c_1912, c_1934])).
% 3.37/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.59  
% 3.37/1.59  Inference rules
% 3.37/1.59  ----------------------
% 3.37/1.59  #Ref     : 0
% 3.37/1.59  #Sup     : 450
% 3.37/1.59  #Fact    : 0
% 3.37/1.59  #Define  : 0
% 3.37/1.59  #Split   : 2
% 3.37/1.59  #Chain   : 0
% 3.37/1.59  #Close   : 0
% 3.37/1.59  
% 3.37/1.59  Ordering : KBO
% 3.37/1.59  
% 3.37/1.59  Simplification rules
% 3.37/1.59  ----------------------
% 3.37/1.59  #Subsume      : 79
% 3.37/1.59  #Demod        : 585
% 3.37/1.59  #Tautology    : 234
% 3.37/1.59  #SimpNegUnit  : 2
% 3.37/1.59  #BackRed      : 31
% 3.37/1.59  
% 3.37/1.59  #Partial instantiations: 0
% 3.37/1.59  #Strategies tried      : 1
% 3.37/1.59  
% 3.37/1.59  Timing (in seconds)
% 3.37/1.59  ----------------------
% 3.37/1.59  Preprocessing        : 0.31
% 3.37/1.59  Parsing              : 0.16
% 3.37/1.59  CNF conversion       : 0.02
% 3.37/1.59  Main loop            : 0.48
% 3.37/1.59  Inferencing          : 0.16
% 3.37/1.59  Reduction            : 0.14
% 3.37/1.59  Demodulation         : 0.10
% 3.37/1.60  BG Simplification    : 0.02
% 3.37/1.60  Subsumption          : 0.11
% 3.37/1.60  Abstraction          : 0.02
% 3.37/1.60  MUC search           : 0.00
% 3.37/1.60  Cooper               : 0.00
% 3.37/1.60  Total                : 0.81
% 3.37/1.60  Index Insertion      : 0.00
% 3.37/1.60  Index Deletion       : 0.00
% 3.37/1.60  Index Matching       : 0.00
% 3.37/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
