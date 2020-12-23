%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:54 EST 2020

% Result     : Theorem 9.52s
% Output     : CNFRefutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 145 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  135 ( 323 expanded)
%              Number of equality atoms :   60 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_61,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_83,axiom,(
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

tff(c_60,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_105,plain,(
    ! [A_68,B_69] :
      ( k9_relat_1(A_68,k1_tarski(B_69)) = k11_relat_1(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_81] :
      ( k9_relat_1(A_81,k1_relat_1('#skF_9')) = k11_relat_1(A_81,'#skF_8')
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_30,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_172,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_30])).

tff(c_182,plain,(
    k11_relat_1('#skF_9','#skF_8') = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_172])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [D_60,B_61] : r2_hidden(D_60,k2_tarski(D_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_64] : r2_hidden(A_64,k1_tarski(A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_74])).

tff(c_85,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_82])).

tff(c_215,plain,(
    ! [B_84,A_85] :
      ( k11_relat_1(B_84,A_85) != k1_xboole_0
      | ~ r2_hidden(A_85,k1_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_225,plain,
    ( k11_relat_1('#skF_9','#skF_8') != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_85,c_215])).

tff(c_230,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_182,c_225])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [A_19,C_55] :
      ( r2_hidden('#skF_7'(A_19,k2_relat_1(A_19),C_55),k1_relat_1(A_19))
      | ~ r2_hidden(C_55,k2_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_19,D_58] :
      ( r2_hidden(k1_funct_1(A_19,D_58),k2_relat_1(A_19))
      | ~ r2_hidden(D_58,k1_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2975,plain,(
    ! [A_2936,C_2937] :
      ( r2_hidden('#skF_7'(A_2936,k2_relat_1(A_2936),C_2937),k1_relat_1(A_2936))
      | ~ r2_hidden(C_2937,k2_relat_1(A_2936))
      | ~ v1_funct_1(A_2936)
      | ~ v1_relat_1(A_2936) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_118,plain,(
    ! [D_72,B_73,A_74] :
      ( D_72 = B_73
      | D_72 = A_74
      | ~ r2_hidden(D_72,k2_tarski(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [D_77,A_78] :
      ( D_77 = A_78
      | D_77 = A_78
      | ~ r2_hidden(D_77,k1_tarski(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_139,plain,(
    ! [D_77] :
      ( D_77 = '#skF_8'
      | D_77 = '#skF_8'
      | ~ r2_hidden(D_77,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_133])).

tff(c_2985,plain,(
    ! [C_2937] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_2937) = '#skF_8'
      | ~ r2_hidden(C_2937,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2975,c_139])).

tff(c_3011,plain,(
    ! [C_3000] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_3000) = '#skF_8'
      | ~ r2_hidden(C_3000,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2985])).

tff(c_3015,plain,(
    ! [D_58] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_58)) = '#skF_8'
      | ~ r2_hidden(D_58,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_3011])).

tff(c_3022,plain,(
    ! [D_58] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_58)) = '#skF_8'
      | ~ r2_hidden(D_58,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3015])).

tff(c_5786,plain,(
    ! [A_6794,C_6795] :
      ( k1_funct_1(A_6794,'#skF_7'(A_6794,k2_relat_1(A_6794),C_6795)) = C_6795
      | ~ r2_hidden(C_6795,k2_relat_1(A_6794))
      | ~ v1_funct_1(A_6794)
      | ~ v1_relat_1(A_6794) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5823,plain,(
    ! [D_58] :
      ( k1_funct_1('#skF_9',D_58) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_58),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_58,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3022,c_5786])).

tff(c_14492,plain,(
    ! [D_29297] :
      ( k1_funct_1('#skF_9',D_29297) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_29297),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_29297,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5823])).

tff(c_14521,plain,(
    ! [D_58] :
      ( k1_funct_1('#skF_9',D_58) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_58,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_14492])).

tff(c_14527,plain,(
    ! [D_29577] :
      ( k1_funct_1('#skF_9',D_29577) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_29577,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_14521])).

tff(c_14548,plain,(
    ! [C_55] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_55)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_55,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_14527])).

tff(c_17225,plain,(
    ! [C_36027] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_36027)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_36027,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_14548])).

tff(c_38,plain,(
    ! [A_19,C_55] :
      ( k1_funct_1(A_19,'#skF_7'(A_19,k2_relat_1(A_19),C_55)) = C_55
      | ~ r2_hidden(C_55,k2_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_17281,plain,(
    ! [C_36027] :
      ( k1_funct_1('#skF_9','#skF_8') = C_36027
      | ~ r2_hidden(C_36027,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_36027,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17225,c_38])).

tff(c_17459,plain,(
    ! [C_36589] :
      ( k1_funct_1('#skF_9','#skF_8') = C_36589
      | ~ r2_hidden(C_36589,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_17281])).

tff(c_17495,plain,(
    ! [B_11] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_11) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_11) ) ),
    inference(resolution,[status(thm)],[c_26,c_17459])).

tff(c_17510,plain,(
    ! [B_36869] :
      ( '#skF_3'(k2_relat_1('#skF_9'),B_36869) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_36869) ) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_17495])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( '#skF_3'(A_10,B_11) != B_11
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17521,plain,(
    ! [B_36869] :
      ( k1_funct_1('#skF_9','#skF_8') != B_36869
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_36869)
      | k2_relat_1('#skF_9') = k1_tarski(B_36869) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17510,c_24])).

tff(c_17660,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_17521])).

tff(c_54,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17660,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:41:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.52/3.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.52/3.17  
% 9.52/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.52/3.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_4
% 9.52/3.17  
% 9.52/3.17  %Foreground sorts:
% 9.52/3.17  
% 9.52/3.17  
% 9.52/3.17  %Background operators:
% 9.52/3.17  
% 9.52/3.17  
% 9.52/3.17  %Foreground operators:
% 9.52/3.17  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.52/3.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.52/3.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.52/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.52/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.52/3.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.52/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.52/3.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.52/3.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.52/3.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.52/3.17  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 9.52/3.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.52/3.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.52/3.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.52/3.17  tff('#skF_9', type, '#skF_9': $i).
% 9.52/3.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.52/3.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.52/3.17  tff('#skF_8', type, '#skF_8': $i).
% 9.52/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.52/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.52/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.52/3.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.52/3.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.52/3.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.52/3.17  
% 9.52/3.18  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 9.52/3.18  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 9.52/3.18  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.52/3.18  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.52/3.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 9.52/3.18  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 9.52/3.18  tff(f_52, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 9.52/3.18  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 9.52/3.18  tff(c_60, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.18  tff(c_56, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.18  tff(c_105, plain, (![A_68, B_69]: (k9_relat_1(A_68, k1_tarski(B_69))=k11_relat_1(A_68, B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.52/3.18  tff(c_165, plain, (![A_81]: (k9_relat_1(A_81, k1_relat_1('#skF_9'))=k11_relat_1(A_81, '#skF_8') | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_56, c_105])).
% 9.52/3.18  tff(c_30, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.52/3.18  tff(c_172, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_165, c_30])).
% 9.52/3.18  tff(c_182, plain, (k11_relat_1('#skF_9', '#skF_8')=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_172])).
% 9.52/3.18  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.52/3.18  tff(c_74, plain, (![D_60, B_61]: (r2_hidden(D_60, k2_tarski(D_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.52/3.18  tff(c_82, plain, (![A_64]: (r2_hidden(A_64, k1_tarski(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_74])).
% 9.52/3.18  tff(c_85, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_82])).
% 9.52/3.18  tff(c_215, plain, (![B_84, A_85]: (k11_relat_1(B_84, A_85)!=k1_xboole_0 | ~r2_hidden(A_85, k1_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.52/3.18  tff(c_225, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_85, c_215])).
% 9.52/3.18  tff(c_230, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_182, c_225])).
% 9.52/3.18  tff(c_26, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.52/3.18  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.18  tff(c_40, plain, (![A_19, C_55]: (r2_hidden('#skF_7'(A_19, k2_relat_1(A_19), C_55), k1_relat_1(A_19)) | ~r2_hidden(C_55, k2_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.52/3.18  tff(c_36, plain, (![A_19, D_58]: (r2_hidden(k1_funct_1(A_19, D_58), k2_relat_1(A_19)) | ~r2_hidden(D_58, k1_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.52/3.18  tff(c_2975, plain, (![A_2936, C_2937]: (r2_hidden('#skF_7'(A_2936, k2_relat_1(A_2936), C_2937), k1_relat_1(A_2936)) | ~r2_hidden(C_2937, k2_relat_1(A_2936)) | ~v1_funct_1(A_2936) | ~v1_relat_1(A_2936))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.52/3.18  tff(c_118, plain, (![D_72, B_73, A_74]: (D_72=B_73 | D_72=A_74 | ~r2_hidden(D_72, k2_tarski(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.52/3.18  tff(c_133, plain, (![D_77, A_78]: (D_77=A_78 | D_77=A_78 | ~r2_hidden(D_77, k1_tarski(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_118])).
% 9.52/3.18  tff(c_139, plain, (![D_77]: (D_77='#skF_8' | D_77='#skF_8' | ~r2_hidden(D_77, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_133])).
% 9.52/3.18  tff(c_2985, plain, (![C_2937]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_2937)='#skF_8' | ~r2_hidden(C_2937, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2975, c_139])).
% 9.52/3.18  tff(c_3011, plain, (![C_3000]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_3000)='#skF_8' | ~r2_hidden(C_3000, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2985])).
% 9.52/3.18  tff(c_3015, plain, (![D_58]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_58))='#skF_8' | ~r2_hidden(D_58, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_3011])).
% 9.52/3.18  tff(c_3022, plain, (![D_58]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_58))='#skF_8' | ~r2_hidden(D_58, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3015])).
% 9.52/3.18  tff(c_5786, plain, (![A_6794, C_6795]: (k1_funct_1(A_6794, '#skF_7'(A_6794, k2_relat_1(A_6794), C_6795))=C_6795 | ~r2_hidden(C_6795, k2_relat_1(A_6794)) | ~v1_funct_1(A_6794) | ~v1_relat_1(A_6794))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.52/3.18  tff(c_5823, plain, (![D_58]: (k1_funct_1('#skF_9', D_58)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_58), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_58, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_3022, c_5786])).
% 9.52/3.18  tff(c_14492, plain, (![D_29297]: (k1_funct_1('#skF_9', D_29297)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_29297), k2_relat_1('#skF_9')) | ~r2_hidden(D_29297, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5823])).
% 9.52/3.18  tff(c_14521, plain, (![D_58]: (k1_funct_1('#skF_9', D_58)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_58, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_14492])).
% 9.52/3.18  tff(c_14527, plain, (![D_29577]: (k1_funct_1('#skF_9', D_29577)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_29577, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_14521])).
% 9.52/3.18  tff(c_14548, plain, (![C_55]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_55))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_55, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_14527])).
% 9.52/3.18  tff(c_17225, plain, (![C_36027]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_36027))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_36027, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_14548])).
% 9.52/3.18  tff(c_38, plain, (![A_19, C_55]: (k1_funct_1(A_19, '#skF_7'(A_19, k2_relat_1(A_19), C_55))=C_55 | ~r2_hidden(C_55, k2_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.52/3.18  tff(c_17281, plain, (![C_36027]: (k1_funct_1('#skF_9', '#skF_8')=C_36027 | ~r2_hidden(C_36027, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_36027, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_17225, c_38])).
% 9.52/3.18  tff(c_17459, plain, (![C_36589]: (k1_funct_1('#skF_9', '#skF_8')=C_36589 | ~r2_hidden(C_36589, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_17281])).
% 9.52/3.18  tff(c_17495, plain, (![B_11]: ('#skF_3'(k2_relat_1('#skF_9'), B_11)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_11))), inference(resolution, [status(thm)], [c_26, c_17459])).
% 9.52/3.18  tff(c_17510, plain, (![B_36869]: ('#skF_3'(k2_relat_1('#skF_9'), B_36869)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_36869))), inference(negUnitSimplification, [status(thm)], [c_230, c_17495])).
% 9.52/3.18  tff(c_24, plain, (![A_10, B_11]: ('#skF_3'(A_10, B_11)!=B_11 | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.52/3.18  tff(c_17521, plain, (![B_36869]: (k1_funct_1('#skF_9', '#skF_8')!=B_36869 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_36869) | k2_relat_1('#skF_9')=k1_tarski(B_36869))), inference(superposition, [status(thm), theory('equality')], [c_17510, c_24])).
% 9.52/3.18  tff(c_17660, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_230, c_17521])).
% 9.52/3.18  tff(c_54, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.18  tff(c_17664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17660, c_54])).
% 9.52/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.52/3.18  
% 9.52/3.18  Inference rules
% 9.52/3.18  ----------------------
% 9.52/3.18  #Ref     : 8
% 9.52/3.18  #Sup     : 3101
% 9.52/3.18  #Fact    : 13
% 9.52/3.18  #Define  : 0
% 9.52/3.18  #Split   : 8
% 9.52/3.18  #Chain   : 0
% 9.52/3.18  #Close   : 0
% 9.52/3.18  
% 9.52/3.18  Ordering : KBO
% 9.52/3.18  
% 9.52/3.18  Simplification rules
% 9.52/3.18  ----------------------
% 9.52/3.18  #Subsume      : 1293
% 9.52/3.18  #Demod        : 674
% 9.52/3.18  #Tautology    : 754
% 9.52/3.18  #SimpNegUnit  : 220
% 9.52/3.18  #BackRed      : 25
% 9.52/3.18  
% 9.52/3.18  #Partial instantiations: 20614
% 9.52/3.18  #Strategies tried      : 1
% 9.52/3.18  
% 9.52/3.18  Timing (in seconds)
% 9.52/3.18  ----------------------
% 9.52/3.18  Preprocessing        : 0.33
% 9.52/3.18  Parsing              : 0.16
% 9.52/3.18  CNF conversion       : 0.03
% 9.52/3.18  Main loop            : 2.11
% 9.52/3.18  Inferencing          : 0.84
% 9.52/3.18  Reduction            : 0.54
% 9.52/3.19  Demodulation         : 0.37
% 9.52/3.19  BG Simplification    : 0.08
% 9.52/3.19  Subsumption          : 0.55
% 9.52/3.19  Abstraction          : 0.10
% 9.52/3.19  MUC search           : 0.00
% 9.52/3.19  Cooper               : 0.00
% 9.52/3.19  Total                : 2.46
% 9.52/3.19  Index Insertion      : 0.00
% 9.52/3.19  Index Deletion       : 0.00
% 9.52/3.19  Index Matching       : 0.00
% 9.52/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
