%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   20
%              Number of atoms          :  135 ( 323 expanded)
%              Number of equality atoms :   60 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_87,axiom,(
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

tff(c_64,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_138,plain,(
    ! [A_81,B_82] :
      ( k9_relat_1(A_81,k1_tarski(B_82)) = k11_relat_1(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [A_88] :
      ( k9_relat_1(A_88,k1_relat_1('#skF_9')) = k11_relat_1(A_88,'#skF_8')
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_138])).

tff(c_34,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_34])).

tff(c_177,plain,(
    k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_167])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    ! [D_67,B_68] : r2_hidden(D_67,k2_tarski(D_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_71] : r2_hidden(A_71,k1_tarski(A_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_78])).

tff(c_89,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_86])).

tff(c_202,plain,(
    ! [B_91,A_92] :
      ( k11_relat_1(B_91,A_92) != k1_xboole_0
      | ~ r2_hidden(A_92,k1_relat_1(B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_209,plain,
    ( k11_relat_1('#skF_9','#skF_8') != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_89,c_202])).

tff(c_213,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_177,c_209])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_3'(A_17,B_18),A_17)
      | k1_xboole_0 = A_17
      | k1_tarski(B_18) = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [A_26,C_62] :
      ( r2_hidden('#skF_7'(A_26,k2_relat_1(A_26),C_62),k1_relat_1(A_26))
      | ~ r2_hidden(C_62,k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    ! [A_26,D_65] :
      ( r2_hidden(k1_funct_1(A_26,D_65),k2_relat_1(A_26))
      | ~ r2_hidden(D_65,k1_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6555,plain,(
    ! [A_8403,C_8404] :
      ( r2_hidden('#skF_7'(A_8403,k2_relat_1(A_8403),C_8404),k1_relat_1(A_8403))
      | ~ r2_hidden(C_8404,k2_relat_1(A_8403))
      | ~ v1_funct_1(A_8403)
      | ~ v1_relat_1(A_8403) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_109,plain,(
    ! [D_75,B_76,A_77] :
      ( D_75 = B_76
      | D_75 = A_77
      | ~ r2_hidden(D_75,k2_tarski(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [D_78,A_79] :
      ( D_78 = A_79
      | D_78 = A_79
      | ~ r2_hidden(D_78,k1_tarski(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_109])).

tff(c_129,plain,(
    ! [D_78] :
      ( D_78 = '#skF_8'
      | D_78 = '#skF_8'
      | ~ r2_hidden(D_78,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_123])).

tff(c_6565,plain,(
    ! [C_8404] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_8404) = '#skF_8'
      | ~ r2_hidden(C_8404,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6555,c_129])).

tff(c_6609,plain,(
    ! [C_8565] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_8565) = '#skF_8'
      | ~ r2_hidden(C_8565,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6565])).

tff(c_6613,plain,(
    ! [D_65] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_65)) = '#skF_8'
      | ~ r2_hidden(D_65,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_6609])).

tff(c_6620,plain,(
    ! [D_65] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_65)) = '#skF_8'
      | ~ r2_hidden(D_65,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6613])).

tff(c_8550,plain,(
    ! [A_12055,C_12056] :
      ( k1_funct_1(A_12055,'#skF_7'(A_12055,k2_relat_1(A_12055),C_12056)) = C_12056
      | ~ r2_hidden(C_12056,k2_relat_1(A_12055))
      | ~ v1_funct_1(A_12055)
      | ~ v1_relat_1(A_12055) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8575,plain,(
    ! [D_65] :
      ( k1_funct_1('#skF_9',D_65) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_65),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_65,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6620,c_8550])).

tff(c_9413,plain,(
    ! [D_13873] :
      ( k1_funct_1('#skF_9',D_13873) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_13873),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_13873,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8575])).

tff(c_9436,plain,(
    ! [D_65] :
      ( k1_funct_1('#skF_9',D_65) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_65,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_9413])).

tff(c_9442,plain,(
    ! [D_14074] :
      ( k1_funct_1('#skF_9',D_14074) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_14074,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_9436])).

tff(c_9446,plain,(
    ! [C_62] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_62)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_62,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_9442])).

tff(c_16861,plain,(
    ! [C_39411] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_39411)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_39411,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_9446])).

tff(c_42,plain,(
    ! [A_26,C_62] :
      ( k1_funct_1(A_26,'#skF_7'(A_26,k2_relat_1(A_26),C_62)) = C_62
      | ~ r2_hidden(C_62,k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16915,plain,(
    ! [C_39411] :
      ( k1_funct_1('#skF_9','#skF_8') = C_39411
      | ~ r2_hidden(C_39411,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_39411,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16861,c_42])).

tff(c_17017,plain,(
    ! [C_39732] :
      ( k1_funct_1('#skF_9','#skF_8') = C_39732
      | ~ r2_hidden(C_39732,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_16915])).

tff(c_17052,plain,(
    ! [B_18] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_18) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_18) ) ),
    inference(resolution,[status(thm)],[c_30,c_17017])).

tff(c_17096,plain,(
    ! [B_40374] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_40374) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_40374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_17052])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( '#skF_3'(A_17,B_18) != B_18
      | k1_xboole_0 = A_17
      | k1_tarski(B_18) = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_17107,plain,(
    ! [B_40374] :
      ( k1_funct_1('#skF_9','#skF_8') != B_40374
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_40374)
      | k2_relat_1('#skF_9') = k1_tarski(B_40374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17096,c_28])).

tff(c_17256,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_17107])).

tff(c_58,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17256,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.09  
% 8.87/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.10  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4
% 8.87/3.10  
% 8.87/3.10  %Foreground sorts:
% 8.87/3.10  
% 8.87/3.10  
% 8.87/3.10  %Background operators:
% 8.87/3.10  
% 8.87/3.10  
% 8.87/3.10  %Foreground operators:
% 8.87/3.10  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.87/3.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.87/3.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.87/3.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/3.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.87/3.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.87/3.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.87/3.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.87/3.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.87/3.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.87/3.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.87/3.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.87/3.10  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 8.87/3.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.87/3.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.87/3.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.87/3.10  tff('#skF_9', type, '#skF_9': $i).
% 8.87/3.10  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.87/3.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.87/3.10  tff('#skF_8', type, '#skF_8': $i).
% 8.87/3.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/3.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.87/3.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/3.10  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.87/3.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.87/3.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.87/3.10  
% 8.87/3.11  tff(f_96, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 8.87/3.11  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 8.87/3.11  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.87/3.11  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.87/3.11  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 8.87/3.11  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 8.87/3.11  tff(f_56, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 8.87/3.11  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.87/3.11  tff(c_64, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.87/3.11  tff(c_60, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.87/3.11  tff(c_138, plain, (![A_81, B_82]: (k9_relat_1(A_81, k1_tarski(B_82))=k11_relat_1(A_81, B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.87/3.11  tff(c_160, plain, (![A_88]: (k9_relat_1(A_88, k1_relat_1('#skF_9'))=k11_relat_1(A_88, '#skF_8') | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_60, c_138])).
% 8.87/3.11  tff(c_34, plain, (![A_23]: (k9_relat_1(A_23, k1_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.87/3.11  tff(c_167, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_160, c_34])).
% 8.87/3.11  tff(c_177, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_167])).
% 8.87/3.11  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.87/3.11  tff(c_78, plain, (![D_67, B_68]: (r2_hidden(D_67, k2_tarski(D_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/3.11  tff(c_86, plain, (![A_71]: (r2_hidden(A_71, k1_tarski(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_78])).
% 8.87/3.11  tff(c_89, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_86])).
% 8.87/3.11  tff(c_202, plain, (![B_91, A_92]: (k11_relat_1(B_91, A_92)!=k1_xboole_0 | ~r2_hidden(A_92, k1_relat_1(B_91)) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.87/3.11  tff(c_209, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_89, c_202])).
% 8.87/3.11  tff(c_213, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_177, c_209])).
% 8.87/3.11  tff(c_30, plain, (![A_17, B_18]: (r2_hidden('#skF_3'(A_17, B_18), A_17) | k1_xboole_0=A_17 | k1_tarski(B_18)=A_17)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.87/3.11  tff(c_62, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.87/3.11  tff(c_44, plain, (![A_26, C_62]: (r2_hidden('#skF_7'(A_26, k2_relat_1(A_26), C_62), k1_relat_1(A_26)) | ~r2_hidden(C_62, k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.11  tff(c_40, plain, (![A_26, D_65]: (r2_hidden(k1_funct_1(A_26, D_65), k2_relat_1(A_26)) | ~r2_hidden(D_65, k1_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.11  tff(c_6555, plain, (![A_8403, C_8404]: (r2_hidden('#skF_7'(A_8403, k2_relat_1(A_8403), C_8404), k1_relat_1(A_8403)) | ~r2_hidden(C_8404, k2_relat_1(A_8403)) | ~v1_funct_1(A_8403) | ~v1_relat_1(A_8403))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.11  tff(c_109, plain, (![D_75, B_76, A_77]: (D_75=B_76 | D_75=A_77 | ~r2_hidden(D_75, k2_tarski(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/3.11  tff(c_123, plain, (![D_78, A_79]: (D_78=A_79 | D_78=A_79 | ~r2_hidden(D_78, k1_tarski(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_109])).
% 8.87/3.11  tff(c_129, plain, (![D_78]: (D_78='#skF_8' | D_78='#skF_8' | ~r2_hidden(D_78, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_123])).
% 8.87/3.11  tff(c_6565, plain, (![C_8404]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_8404)='#skF_8' | ~r2_hidden(C_8404, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_6555, c_129])).
% 8.87/3.11  tff(c_6609, plain, (![C_8565]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_8565)='#skF_8' | ~r2_hidden(C_8565, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6565])).
% 8.87/3.11  tff(c_6613, plain, (![D_65]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_65))='#skF_8' | ~r2_hidden(D_65, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_6609])).
% 8.87/3.11  tff(c_6620, plain, (![D_65]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_65))='#skF_8' | ~r2_hidden(D_65, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6613])).
% 8.87/3.11  tff(c_8550, plain, (![A_12055, C_12056]: (k1_funct_1(A_12055, '#skF_7'(A_12055, k2_relat_1(A_12055), C_12056))=C_12056 | ~r2_hidden(C_12056, k2_relat_1(A_12055)) | ~v1_funct_1(A_12055) | ~v1_relat_1(A_12055))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.11  tff(c_8575, plain, (![D_65]: (k1_funct_1('#skF_9', D_65)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_65), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_65, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_6620, c_8550])).
% 8.87/3.11  tff(c_9413, plain, (![D_13873]: (k1_funct_1('#skF_9', D_13873)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_13873), k2_relat_1('#skF_9')) | ~r2_hidden(D_13873, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8575])).
% 8.87/3.11  tff(c_9436, plain, (![D_65]: (k1_funct_1('#skF_9', D_65)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_65, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_9413])).
% 8.87/3.11  tff(c_9442, plain, (![D_14074]: (k1_funct_1('#skF_9', D_14074)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_14074, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_9436])).
% 8.87/3.11  tff(c_9446, plain, (![C_62]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_62))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_62, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_9442])).
% 8.87/3.11  tff(c_16861, plain, (![C_39411]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_39411))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_39411, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_9446])).
% 8.87/3.11  tff(c_42, plain, (![A_26, C_62]: (k1_funct_1(A_26, '#skF_7'(A_26, k2_relat_1(A_26), C_62))=C_62 | ~r2_hidden(C_62, k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.11  tff(c_16915, plain, (![C_39411]: (k1_funct_1('#skF_9', '#skF_8')=C_39411 | ~r2_hidden(C_39411, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_39411, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_16861, c_42])).
% 8.87/3.11  tff(c_17017, plain, (![C_39732]: (k1_funct_1('#skF_9', '#skF_8')=C_39732 | ~r2_hidden(C_39732, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_16915])).
% 8.87/3.11  tff(c_17052, plain, (![B_18]: ('#skF_3'(k2_relat_1('#skF_9'), B_18)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_18))), inference(resolution, [status(thm)], [c_30, c_17017])).
% 8.87/3.11  tff(c_17096, plain, (![B_40374]: ('#skF_3'(k2_relat_1('#skF_9'), B_40374)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_40374))), inference(negUnitSimplification, [status(thm)], [c_213, c_17052])).
% 8.87/3.11  tff(c_28, plain, (![A_17, B_18]: ('#skF_3'(A_17, B_18)!=B_18 | k1_xboole_0=A_17 | k1_tarski(B_18)=A_17)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.87/3.11  tff(c_17107, plain, (![B_40374]: (k1_funct_1('#skF_9', '#skF_8')!=B_40374 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_40374) | k2_relat_1('#skF_9')=k1_tarski(B_40374))), inference(superposition, [status(thm), theory('equality')], [c_17096, c_28])).
% 8.87/3.11  tff(c_17256, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_213, c_17107])).
% 8.87/3.11  tff(c_58, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.87/3.11  tff(c_17260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17256, c_58])).
% 8.87/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.87/3.11  
% 8.87/3.11  Inference rules
% 8.87/3.11  ----------------------
% 8.87/3.11  #Ref     : 8
% 8.87/3.11  #Sup     : 3080
% 8.87/3.11  #Fact    : 11
% 8.87/3.11  #Define  : 0
% 8.87/3.11  #Split   : 9
% 8.87/3.11  #Chain   : 0
% 8.87/3.11  #Close   : 0
% 8.87/3.11  
% 8.87/3.11  Ordering : KBO
% 8.87/3.11  
% 8.87/3.11  Simplification rules
% 8.87/3.11  ----------------------
% 8.87/3.11  #Subsume      : 1360
% 8.87/3.11  #Demod        : 645
% 8.87/3.11  #Tautology    : 776
% 8.87/3.11  #SimpNegUnit  : 227
% 8.87/3.11  #BackRed      : 33
% 8.87/3.11  
% 8.87/3.11  #Partial instantiations: 20180
% 8.87/3.11  #Strategies tried      : 1
% 8.87/3.11  
% 8.87/3.11  Timing (in seconds)
% 8.87/3.11  ----------------------
% 8.87/3.11  Preprocessing        : 0.32
% 8.87/3.11  Parsing              : 0.16
% 8.87/3.11  CNF conversion       : 0.03
% 8.87/3.12  Main loop            : 1.97
% 8.87/3.12  Inferencing          : 0.79
% 8.87/3.12  Reduction            : 0.51
% 8.87/3.12  Demodulation         : 0.36
% 8.87/3.12  BG Simplification    : 0.07
% 8.87/3.12  Subsumption          : 0.51
% 8.87/3.12  Abstraction          : 0.09
% 8.87/3.12  MUC search           : 0.00
% 8.87/3.12  Cooper               : 0.00
% 8.87/3.12  Total                : 2.32
% 8.87/3.12  Index Insertion      : 0.00
% 8.87/3.12  Index Deletion       : 0.00
% 8.87/3.12  Index Matching       : 0.00
% 8.87/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
