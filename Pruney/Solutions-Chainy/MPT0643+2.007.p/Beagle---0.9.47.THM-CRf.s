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
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 240 expanded)
%              Number of leaves         :   26 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 (1028 expanded)
%              Number of equality atoms :   39 ( 357 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_30,plain,(
    k6_relat_1('#skF_5') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1748,plain,(
    ! [B_193] :
      ( k1_funct_1(B_193,'#skF_4'(k1_relat_1(B_193),B_193)) != '#skF_4'(k1_relat_1(B_193),B_193)
      | k6_relat_1(k1_relat_1(B_193)) = B_193
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1751,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')) != '#skF_4'(k1_relat_1('#skF_7'),'#skF_7')
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1748])).

tff(c_1756,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')) != '#skF_4'('#skF_5','#skF_7')
    | k6_relat_1('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_38,c_1751])).

tff(c_1757,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')) != '#skF_4'('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1756])).

tff(c_62,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_134,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_4'(k1_relat_1(B_47),B_47),k1_relat_1(B_47))
      | k6_relat_1(k1_relat_1(B_47)) = B_47
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_139,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_134])).

tff(c_151,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_5')
    | k6_relat_1('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_38,c_139])).

tff(c_152,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_151])).

tff(c_36,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_123,plain,(
    ! [B_43,A_44] :
      ( r2_hidden(k1_funct_1(B_43,A_44),k2_relat_1(B_43))
      | ~ r2_hidden(A_44,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [B_43,A_44,B_2] :
      ( r2_hidden(k1_funct_1(B_43,A_44),B_2)
      | ~ r1_tarski(k2_relat_1(B_43),B_2)
      | ~ r2_hidden(A_44,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    k5_relat_1('#skF_7','#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_162,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_7'),B_2)
      | ~ r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_1897,plain,(
    ! [C_233,B_234,A_235] :
      ( k1_funct_1(k5_relat_1(C_233,B_234),A_235) = k1_funct_1(B_234,k1_funct_1(C_233,A_235))
      | ~ r2_hidden(A_235,k1_relat_1(k5_relat_1(C_233,B_234)))
      | ~ v1_funct_1(C_233)
      | ~ v1_relat_1(C_233)
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2021,plain,(
    ! [C_240,B_241] :
      ( k1_funct_1(k5_relat_1(C_240,B_241),'#skF_4'('#skF_5','#skF_7')) = k1_funct_1(B_241,k1_funct_1(C_240,'#skF_4'('#skF_5','#skF_7')))
      | ~ v1_funct_1(C_240)
      | ~ v1_relat_1(C_240)
      | ~ v1_funct_1(B_241)
      | ~ v1_relat_1(B_241)
      | ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1(C_240,B_241))) ) ),
    inference(resolution,[status(thm)],[c_162,c_1897])).

tff(c_2024,plain,
    ( k1_funct_1(k5_relat_1('#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7')) = k1_funct_1('#skF_6',k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2021])).

tff(c_2026,plain,(
    k1_funct_1('#skF_6',k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7'))) = k1_funct_1('#skF_6','#skF_4'('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_40,c_48,c_46,c_44,c_42,c_32,c_2024])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(k1_funct_1(B_14,A_13),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2064,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'('#skF_5','#skF_7')),k2_relat_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2026,c_18])).

tff(c_2080,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'('#skF_5','#skF_7')),k2_relat_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_2064])).

tff(c_2097,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2080])).

tff(c_2100,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_129,c_2097])).

tff(c_2104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_152,c_38,c_36,c_2100])).

tff(c_2106,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2080])).

tff(c_2109,plain,(
    ! [B_2] :
      ( r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')),B_2)
      | ~ r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_2106,c_2])).

tff(c_34,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1948,plain,(
    ! [A_235] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_6'),A_235) = k1_funct_1('#skF_6',k1_funct_1('#skF_7',A_235))
      | ~ r2_hidden(A_235,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1897])).

tff(c_1963,plain,(
    ! [A_236] :
      ( k1_funct_1('#skF_6',k1_funct_1('#skF_7',A_236)) = k1_funct_1('#skF_6',A_236)
      | ~ r2_hidden(A_236,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_32,c_1948])).

tff(c_8,plain,(
    ! [C_12,B_11,A_6] :
      ( C_12 = B_11
      | k1_funct_1(A_6,C_12) != k1_funct_1(A_6,B_11)
      | ~ r2_hidden(C_12,k1_relat_1(A_6))
      | ~ r2_hidden(B_11,k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1971,plain,(
    ! [A_236,B_11] :
      ( k1_funct_1('#skF_7',A_236) = B_11
      | k1_funct_1('#skF_6',B_11) != k1_funct_1('#skF_6',A_236)
      | ~ r2_hidden(k1_funct_1('#skF_7',A_236),k1_relat_1('#skF_6'))
      | ~ r2_hidden(B_11,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_236,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1963,c_8])).

tff(c_1988,plain,(
    ! [A_236,B_11] :
      ( k1_funct_1('#skF_7',A_236) = B_11
      | k1_funct_1('#skF_6',B_11) != k1_funct_1('#skF_6',A_236)
      | ~ r2_hidden(k1_funct_1('#skF_7',A_236),'#skF_5')
      | ~ r2_hidden(B_11,'#skF_5')
      | ~ r2_hidden(A_236,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_40,c_40,c_1971])).

tff(c_2349,plain,(
    ! [A_277] :
      ( k1_funct_1('#skF_7',A_277) = A_277
      | ~ r2_hidden(k1_funct_1('#skF_7',A_277),'#skF_5')
      | ~ r2_hidden(A_277,'#skF_5')
      | ~ r2_hidden(A_277,'#skF_5') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1988])).

tff(c_2360,plain,
    ( k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')) = '#skF_4'('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_2109,c_2349])).

tff(c_2378,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_5','#skF_7')) = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_152,c_2360])).

tff(c_2380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1757,c_2378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.93  
% 4.88/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.93  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 4.88/1.93  
% 4.88/1.93  %Foreground sorts:
% 4.88/1.93  
% 4.88/1.93  
% 4.88/1.93  %Background operators:
% 4.88/1.93  
% 4.88/1.93  
% 4.88/1.93  %Foreground operators:
% 4.88/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.88/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/1.93  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.88/1.93  tff('#skF_7', type, '#skF_7': $i).
% 4.88/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.88/1.93  tff('#skF_6', type, '#skF_6': $i).
% 4.88/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.93  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.88/1.93  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.88/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.88/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/1.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.88/1.93  
% 4.88/1.95  tff(f_103, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 4.88/1.95  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 4.88/1.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.88/1.95  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.88/1.95  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 4.88/1.95  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.88/1.95  tff(c_30, plain, (k6_relat_1('#skF_5')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_44, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_38, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_1748, plain, (![B_193]: (k1_funct_1(B_193, '#skF_4'(k1_relat_1(B_193), B_193))!='#skF_4'(k1_relat_1(B_193), B_193) | k6_relat_1(k1_relat_1(B_193))=B_193 | ~v1_funct_1(B_193) | ~v1_relat_1(B_193))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.95  tff(c_1751, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))!='#skF_4'(k1_relat_1('#skF_7'), '#skF_7') | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1748])).
% 4.88/1.95  tff(c_1756, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))!='#skF_4'('#skF_5', '#skF_7') | k6_relat_1('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_1751])).
% 4.88/1.95  tff(c_1757, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))!='#skF_4'('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_30, c_1756])).
% 4.88/1.95  tff(c_62, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.95  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.95  tff(c_67, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(resolution, [status(thm)], [c_62, c_4])).
% 4.88/1.95  tff(c_134, plain, (![B_47]: (r2_hidden('#skF_4'(k1_relat_1(B_47), B_47), k1_relat_1(B_47)) | k6_relat_1(k1_relat_1(B_47))=B_47 | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.88/1.95  tff(c_139, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_38, c_134])).
% 4.88/1.95  tff(c_151, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_5') | k6_relat_1('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_139])).
% 4.88/1.95  tff(c_152, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_151])).
% 4.88/1.95  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_123, plain, (![B_43, A_44]: (r2_hidden(k1_funct_1(B_43, A_44), k2_relat_1(B_43)) | ~r2_hidden(A_44, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.95  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.95  tff(c_129, plain, (![B_43, A_44, B_2]: (r2_hidden(k1_funct_1(B_43, A_44), B_2) | ~r1_tarski(k2_relat_1(B_43), B_2) | ~r2_hidden(A_44, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_123, c_2])).
% 4.88/1.95  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_40, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_32, plain, (k5_relat_1('#skF_7', '#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_162, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_5', '#skF_7'), B_2) | ~r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_152, c_2])).
% 4.88/1.95  tff(c_1897, plain, (![C_233, B_234, A_235]: (k1_funct_1(k5_relat_1(C_233, B_234), A_235)=k1_funct_1(B_234, k1_funct_1(C_233, A_235)) | ~r2_hidden(A_235, k1_relat_1(k5_relat_1(C_233, B_234))) | ~v1_funct_1(C_233) | ~v1_relat_1(C_233) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.88/1.95  tff(c_2021, plain, (![C_240, B_241]: (k1_funct_1(k5_relat_1(C_240, B_241), '#skF_4'('#skF_5', '#skF_7'))=k1_funct_1(B_241, k1_funct_1(C_240, '#skF_4'('#skF_5', '#skF_7'))) | ~v1_funct_1(C_240) | ~v1_relat_1(C_240) | ~v1_funct_1(B_241) | ~v1_relat_1(B_241) | ~r1_tarski('#skF_5', k1_relat_1(k5_relat_1(C_240, B_241))))), inference(resolution, [status(thm)], [c_162, c_1897])).
% 4.88/1.95  tff(c_2024, plain, (k1_funct_1(k5_relat_1('#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7'))=k1_funct_1('#skF_6', k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2021])).
% 4.88/1.95  tff(c_2026, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')))=k1_funct_1('#skF_6', '#skF_4'('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_40, c_48, c_46, c_44, c_42, c_32, c_2024])).
% 4.88/1.95  tff(c_18, plain, (![B_14, A_13]: (r2_hidden(k1_funct_1(B_14, A_13), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.95  tff(c_2064, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'('#skF_5', '#skF_7')), k2_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2026, c_18])).
% 4.88/1.95  tff(c_2080, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'('#skF_5', '#skF_7')), k2_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_2064])).
% 4.88/1.95  tff(c_2097, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_5')), inference(splitLeft, [status(thm)], [c_2080])).
% 4.88/1.95  tff(c_2100, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_5') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_129, c_2097])).
% 4.88/1.95  tff(c_2104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_152, c_38, c_36, c_2100])).
% 4.88/1.95  tff(c_2106, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_5')), inference(splitRight, [status(thm)], [c_2080])).
% 4.88/1.95  tff(c_2109, plain, (![B_2]: (r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7')), B_2) | ~r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_2106, c_2])).
% 4.88/1.95  tff(c_34, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.95  tff(c_1948, plain, (![A_235]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_6'), A_235)=k1_funct_1('#skF_6', k1_funct_1('#skF_7', A_235)) | ~r2_hidden(A_235, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1897])).
% 4.88/1.95  tff(c_1963, plain, (![A_236]: (k1_funct_1('#skF_6', k1_funct_1('#skF_7', A_236))=k1_funct_1('#skF_6', A_236) | ~r2_hidden(A_236, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_32, c_1948])).
% 4.88/1.95  tff(c_8, plain, (![C_12, B_11, A_6]: (C_12=B_11 | k1_funct_1(A_6, C_12)!=k1_funct_1(A_6, B_11) | ~r2_hidden(C_12, k1_relat_1(A_6)) | ~r2_hidden(B_11, k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/1.95  tff(c_1971, plain, (![A_236, B_11]: (k1_funct_1('#skF_7', A_236)=B_11 | k1_funct_1('#skF_6', B_11)!=k1_funct_1('#skF_6', A_236) | ~r2_hidden(k1_funct_1('#skF_7', A_236), k1_relat_1('#skF_6')) | ~r2_hidden(B_11, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_236, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1963, c_8])).
% 4.88/1.95  tff(c_1988, plain, (![A_236, B_11]: (k1_funct_1('#skF_7', A_236)=B_11 | k1_funct_1('#skF_6', B_11)!=k1_funct_1('#skF_6', A_236) | ~r2_hidden(k1_funct_1('#skF_7', A_236), '#skF_5') | ~r2_hidden(B_11, '#skF_5') | ~r2_hidden(A_236, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_40, c_40, c_1971])).
% 4.88/1.95  tff(c_2349, plain, (![A_277]: (k1_funct_1('#skF_7', A_277)=A_277 | ~r2_hidden(k1_funct_1('#skF_7', A_277), '#skF_5') | ~r2_hidden(A_277, '#skF_5') | ~r2_hidden(A_277, '#skF_5'))), inference(reflexivity, [status(thm), theory('equality')], [c_1988])).
% 4.88/1.95  tff(c_2360, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))='#skF_4'('#skF_5', '#skF_7') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_2109, c_2349])).
% 4.88/1.95  tff(c_2378, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_5', '#skF_7'))='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_152, c_2360])).
% 4.88/1.95  tff(c_2380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1757, c_2378])).
% 4.88/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.95  
% 4.88/1.95  Inference rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Ref     : 3
% 4.88/1.95  #Sup     : 530
% 4.88/1.95  #Fact    : 0
% 4.88/1.95  #Define  : 0
% 4.88/1.95  #Split   : 9
% 4.88/1.95  #Chain   : 0
% 4.88/1.95  #Close   : 0
% 4.88/1.95  
% 4.88/1.95  Ordering : KBO
% 4.88/1.95  
% 4.88/1.95  Simplification rules
% 4.88/1.95  ----------------------
% 4.88/1.95  #Subsume      : 126
% 4.88/1.95  #Demod        : 640
% 4.88/1.95  #Tautology    : 148
% 4.88/1.95  #SimpNegUnit  : 11
% 4.88/1.95  #BackRed      : 1
% 4.88/1.95  
% 4.88/1.95  #Partial instantiations: 0
% 4.88/1.95  #Strategies tried      : 1
% 4.88/1.95  
% 4.88/1.95  Timing (in seconds)
% 4.88/1.95  ----------------------
% 4.88/1.95  Preprocessing        : 0.34
% 4.88/1.95  Parsing              : 0.18
% 4.88/1.95  CNF conversion       : 0.03
% 4.88/1.95  Main loop            : 0.78
% 4.88/1.95  Inferencing          : 0.29
% 4.88/1.95  Reduction            : 0.24
% 4.88/1.95  Demodulation         : 0.16
% 4.88/1.95  BG Simplification    : 0.03
% 4.88/1.95  Subsumption          : 0.16
% 4.88/1.95  Abstraction          : 0.04
% 4.88/1.95  MUC search           : 0.00
% 4.88/1.95  Cooper               : 0.00
% 4.88/1.95  Total                : 1.15
% 4.88/1.95  Index Insertion      : 0.00
% 4.88/1.95  Index Deletion       : 0.00
% 4.88/1.95  Index Matching       : 0.00
% 4.88/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
