%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 189 expanded)
%              Number of equality atoms :   55 (  80 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,axiom,(
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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    ! [A_14,B_15] : v1_funct_1('#skF_4'(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_14,B_15] : k1_relat_1('#skF_4'(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_14,B_15] : v1_relat_1('#skF_4'(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_21] : v1_funct_1('#skF_5'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_21] : k1_relat_1('#skF_5'(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_21] : v1_relat_1('#skF_5'(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_77,plain,(
    ! [C_46,B_47] :
      ( C_46 = B_47
      | k1_relat_1(C_46) != '#skF_6'
      | k1_relat_1(B_47) != '#skF_6'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_81,plain,(
    ! [B_47,A_21] :
      ( B_47 = '#skF_5'(A_21)
      | k1_relat_1('#skF_5'(A_21)) != '#skF_6'
      | k1_relat_1(B_47) != '#skF_6'
      | ~ v1_funct_1('#skF_5'(A_21))
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_44,c_77])).

tff(c_154,plain,(
    ! [B_72,A_73] :
      ( B_72 = '#skF_5'(A_73)
      | A_73 != '#skF_6'
      | k1_relat_1(B_72) != '#skF_6'
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_81])).

tff(c_156,plain,(
    ! [A_73,A_14,B_15] :
      ( '#skF_5'(A_73) = '#skF_4'(A_14,B_15)
      | A_73 != '#skF_6'
      | k1_relat_1('#skF_4'(A_14,B_15)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_223,plain,(
    ! [A_78,A_79,B_80] :
      ( '#skF_5'(A_78) = '#skF_4'(A_79,B_80)
      | A_78 != '#skF_6'
      | A_79 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_156])).

tff(c_30,plain,(
    ! [A_14,B_15,D_20] :
      ( k1_funct_1('#skF_4'(A_14,B_15),D_20) = B_15
      | ~ r2_hidden(D_20,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_515,plain,(
    ! [A_123,D_124,B_125,A_126] :
      ( k1_funct_1('#skF_5'(A_123),D_124) = B_125
      | ~ r2_hidden(D_124,A_126)
      | A_123 != '#skF_6'
      | A_126 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_30])).

tff(c_6000,plain,(
    ! [A_437,A_438,B_439] :
      ( k1_funct_1('#skF_5'(A_437),'#skF_3'(A_438,B_439)) = '#skF_6'
      | A_437 != '#skF_6'
      | A_438 != '#skF_6'
      | r1_xboole_0(A_438,B_439) ) ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_38,plain,(
    ! [A_21,C_26] :
      ( k1_funct_1('#skF_5'(A_21),C_26) = k1_xboole_0
      | ~ r2_hidden(C_26,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6003,plain,(
    ! [A_438,B_439,A_437] :
      ( k1_xboole_0 = '#skF_6'
      | ~ r2_hidden('#skF_3'(A_438,B_439),A_437)
      | A_437 != '#skF_6'
      | A_438 != '#skF_6'
      | r1_xboole_0(A_438,B_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6000,c_38])).

tff(c_6721,plain,(
    ! [A_1833,B_1834,A_1835] :
      ( ~ r2_hidden('#skF_3'(A_1833,B_1834),A_1835)
      | A_1835 != '#skF_6'
      | A_1833 != '#skF_6'
      | r1_xboole_0(A_1833,B_1834) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6003])).

tff(c_6754,plain,(
    ! [A_1852,B_1853] :
      ( A_1852 != '#skF_6'
      | r1_xboole_0(A_1852,B_1853) ) ),
    inference(resolution,[status(thm)],[c_28,c_6721])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6763,plain,(
    ! [A_1854,B_1855] :
      ( k3_xboole_0(A_1854,B_1855) = k1_xboole_0
      | A_1854 != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_6754,c_20])).

tff(c_804,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_1'(A_142,B_143,C_144),A_142)
      | r2_hidden('#skF_2'(A_142,B_143,C_144),C_144)
      | k3_xboole_0(A_142,B_143) = C_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_844,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_2'(A_142,B_143,A_142),A_142)
      | k3_xboole_0(A_142,B_143) = A_142 ) ),
    inference(resolution,[status(thm)],[c_804,c_14])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1156,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_1'(A_162,B_163,C_164),B_163)
      | ~ r2_hidden('#skF_2'(A_162,B_163,C_164),B_163)
      | ~ r2_hidden('#skF_2'(A_162,B_163,C_164),A_162)
      | k3_xboole_0(A_162,B_163) = C_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3288,plain,(
    ! [C_375,B_376] :
      ( ~ r2_hidden('#skF_2'(C_375,B_376,C_375),B_376)
      | r2_hidden('#skF_1'(C_375,B_376,C_375),B_376)
      | k3_xboole_0(C_375,B_376) = C_375 ) ),
    inference(resolution,[status(thm)],[c_16,c_1156])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3330,plain,(
    ! [B_377] :
      ( ~ r2_hidden('#skF_2'(B_377,B_377,B_377),B_377)
      | k3_xboole_0(B_377,B_377) = B_377 ) ),
    inference(resolution,[status(thm)],[c_3288,c_8])).

tff(c_3347,plain,(
    ! [B_143] : k3_xboole_0(B_143,B_143) = B_143 ),
    inference(resolution,[status(thm)],[c_844,c_3330])).

tff(c_7054,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6763,c_3347])).

tff(c_7099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7054,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:52:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.32  
% 6.47/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.32  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 6.47/2.32  
% 6.47/2.32  %Foreground sorts:
% 6.47/2.32  
% 6.47/2.32  
% 6.47/2.32  %Background operators:
% 6.47/2.32  
% 6.47/2.32  
% 6.47/2.32  %Foreground operators:
% 6.47/2.32  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.47/2.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.47/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.47/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.47/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.47/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.47/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.47/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.47/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.47/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.47/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.47/2.32  
% 6.47/2.34  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.47/2.34  tff(f_99, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 6.47/2.34  tff(f_68, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 6.47/2.34  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 6.47/2.34  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.47/2.34  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.47/2.34  tff(c_28, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.47/2.34  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.34  tff(c_34, plain, (![A_14, B_15]: (v1_funct_1('#skF_4'(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.34  tff(c_32, plain, (![A_14, B_15]: (k1_relat_1('#skF_4'(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.34  tff(c_36, plain, (![A_14, B_15]: (v1_relat_1('#skF_4'(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.34  tff(c_42, plain, (![A_21]: (v1_funct_1('#skF_5'(A_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.47/2.34  tff(c_40, plain, (![A_21]: (k1_relat_1('#skF_5'(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.47/2.34  tff(c_44, plain, (![A_21]: (v1_relat_1('#skF_5'(A_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.47/2.34  tff(c_77, plain, (![C_46, B_47]: (C_46=B_47 | k1_relat_1(C_46)!='#skF_6' | k1_relat_1(B_47)!='#skF_6' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.47/2.34  tff(c_81, plain, (![B_47, A_21]: (B_47='#skF_5'(A_21) | k1_relat_1('#skF_5'(A_21))!='#skF_6' | k1_relat_1(B_47)!='#skF_6' | ~v1_funct_1('#skF_5'(A_21)) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_44, c_77])).
% 6.47/2.34  tff(c_154, plain, (![B_72, A_73]: (B_72='#skF_5'(A_73) | A_73!='#skF_6' | k1_relat_1(B_72)!='#skF_6' | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_81])).
% 6.47/2.34  tff(c_156, plain, (![A_73, A_14, B_15]: ('#skF_5'(A_73)='#skF_4'(A_14, B_15) | A_73!='#skF_6' | k1_relat_1('#skF_4'(A_14, B_15))!='#skF_6' | ~v1_funct_1('#skF_4'(A_14, B_15)))), inference(resolution, [status(thm)], [c_36, c_154])).
% 6.47/2.34  tff(c_223, plain, (![A_78, A_79, B_80]: ('#skF_5'(A_78)='#skF_4'(A_79, B_80) | A_78!='#skF_6' | A_79!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_156])).
% 6.47/2.34  tff(c_30, plain, (![A_14, B_15, D_20]: (k1_funct_1('#skF_4'(A_14, B_15), D_20)=B_15 | ~r2_hidden(D_20, A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.47/2.34  tff(c_515, plain, (![A_123, D_124, B_125, A_126]: (k1_funct_1('#skF_5'(A_123), D_124)=B_125 | ~r2_hidden(D_124, A_126) | A_123!='#skF_6' | A_126!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_223, c_30])).
% 6.47/2.34  tff(c_6000, plain, (![A_437, A_438, B_439]: (k1_funct_1('#skF_5'(A_437), '#skF_3'(A_438, B_439))='#skF_6' | A_437!='#skF_6' | A_438!='#skF_6' | r1_xboole_0(A_438, B_439))), inference(resolution, [status(thm)], [c_28, c_515])).
% 6.47/2.34  tff(c_38, plain, (![A_21, C_26]: (k1_funct_1('#skF_5'(A_21), C_26)=k1_xboole_0 | ~r2_hidden(C_26, A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.47/2.34  tff(c_6003, plain, (![A_438, B_439, A_437]: (k1_xboole_0='#skF_6' | ~r2_hidden('#skF_3'(A_438, B_439), A_437) | A_437!='#skF_6' | A_438!='#skF_6' | r1_xboole_0(A_438, B_439))), inference(superposition, [status(thm), theory('equality')], [c_6000, c_38])).
% 6.47/2.34  tff(c_6721, plain, (![A_1833, B_1834, A_1835]: (~r2_hidden('#skF_3'(A_1833, B_1834), A_1835) | A_1835!='#skF_6' | A_1833!='#skF_6' | r1_xboole_0(A_1833, B_1834))), inference(negUnitSimplification, [status(thm)], [c_46, c_6003])).
% 6.47/2.34  tff(c_6754, plain, (![A_1852, B_1853]: (A_1852!='#skF_6' | r1_xboole_0(A_1852, B_1853))), inference(resolution, [status(thm)], [c_28, c_6721])).
% 6.47/2.34  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.47/2.34  tff(c_6763, plain, (![A_1854, B_1855]: (k3_xboole_0(A_1854, B_1855)=k1_xboole_0 | A_1854!='#skF_6')), inference(resolution, [status(thm)], [c_6754, c_20])).
% 6.47/2.34  tff(c_804, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_1'(A_142, B_143, C_144), A_142) | r2_hidden('#skF_2'(A_142, B_143, C_144), C_144) | k3_xboole_0(A_142, B_143)=C_144)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.47/2.34  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.47/2.34  tff(c_844, plain, (![A_142, B_143]: (r2_hidden('#skF_2'(A_142, B_143, A_142), A_142) | k3_xboole_0(A_142, B_143)=A_142)), inference(resolution, [status(thm)], [c_804, c_14])).
% 6.47/2.34  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.47/2.34  tff(c_1156, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_1'(A_162, B_163, C_164), B_163) | ~r2_hidden('#skF_2'(A_162, B_163, C_164), B_163) | ~r2_hidden('#skF_2'(A_162, B_163, C_164), A_162) | k3_xboole_0(A_162, B_163)=C_164)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.47/2.34  tff(c_3288, plain, (![C_375, B_376]: (~r2_hidden('#skF_2'(C_375, B_376, C_375), B_376) | r2_hidden('#skF_1'(C_375, B_376, C_375), B_376) | k3_xboole_0(C_375, B_376)=C_375)), inference(resolution, [status(thm)], [c_16, c_1156])).
% 6.47/2.34  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.47/2.34  tff(c_3330, plain, (![B_377]: (~r2_hidden('#skF_2'(B_377, B_377, B_377), B_377) | k3_xboole_0(B_377, B_377)=B_377)), inference(resolution, [status(thm)], [c_3288, c_8])).
% 6.47/2.34  tff(c_3347, plain, (![B_143]: (k3_xboole_0(B_143, B_143)=B_143)), inference(resolution, [status(thm)], [c_844, c_3330])).
% 6.47/2.34  tff(c_7054, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6763, c_3347])).
% 6.47/2.34  tff(c_7099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7054, c_46])).
% 6.47/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.34  
% 6.47/2.34  Inference rules
% 6.47/2.34  ----------------------
% 6.47/2.34  #Ref     : 3
% 6.47/2.34  #Sup     : 1764
% 6.47/2.34  #Fact    : 0
% 6.47/2.34  #Define  : 0
% 6.47/2.34  #Split   : 2
% 6.47/2.34  #Chain   : 0
% 6.47/2.34  #Close   : 0
% 6.47/2.34  
% 6.47/2.34  Ordering : KBO
% 6.47/2.34  
% 6.47/2.34  Simplification rules
% 6.47/2.34  ----------------------
% 6.47/2.34  #Subsume      : 294
% 6.47/2.34  #Demod        : 649
% 6.47/2.34  #Tautology    : 702
% 6.47/2.34  #SimpNegUnit  : 36
% 6.47/2.34  #BackRed      : 62
% 6.47/2.34  
% 6.47/2.34  #Partial instantiations: 850
% 6.47/2.34  #Strategies tried      : 1
% 6.47/2.34  
% 6.47/2.34  Timing (in seconds)
% 6.47/2.34  ----------------------
% 6.47/2.34  Preprocessing        : 0.33
% 6.47/2.34  Parsing              : 0.17
% 6.47/2.34  CNF conversion       : 0.03
% 6.47/2.34  Main loop            : 1.17
% 6.47/2.34  Inferencing          : 0.38
% 6.47/2.34  Reduction            : 0.35
% 6.47/2.34  Demodulation         : 0.25
% 6.47/2.34  BG Simplification    : 0.06
% 6.47/2.34  Subsumption          : 0.29
% 6.47/2.34  Abstraction          : 0.06
% 6.47/2.34  MUC search           : 0.00
% 6.47/2.34  Cooper               : 0.00
% 6.47/2.34  Total                : 1.52
% 6.47/2.34  Index Insertion      : 0.00
% 6.47/2.34  Index Deletion       : 0.00
% 6.47/2.34  Index Matching       : 0.00
% 6.47/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
