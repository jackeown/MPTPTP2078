%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 172 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 594 expanded)
%              Number of equality atoms :   27 ( 142 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_155,plain,(
    ! [A_60,C_61] :
      ( k1_funct_1(A_60,k1_funct_1(k2_funct_1(A_60),C_61)) = C_61
      | ~ r2_hidden(C_61,k2_relat_1(A_60))
      | ~ v1_funct_1(k2_funct_1(A_60))
      | ~ v1_relat_1(k2_funct_1(A_60))
      | ~ v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),'#skF_6') != '#skF_6'
    | k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_67,plain,(
    k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_175,plain,
    ( ~ r2_hidden('#skF_6',k2_relat_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_67])).

tff(c_190,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_175])).

tff(c_193,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_196,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_196])).

tff(c_201,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_221,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_221])).

tff(c_227,plain,(
    k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [A_31] :
      ( k1_relat_1(k2_funct_1(A_31)) = k2_relat_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_36] : r1_tarski(A_36,A_36) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_44,plain,(
    ! [A_31] :
      ( k2_relat_1(k2_funct_1(A_31)) = k1_relat_1(A_31)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_277,plain,(
    ! [A_78,B_79] :
      ( k1_relat_1(k5_relat_1(A_78,B_79)) = k1_relat_1(A_78)
      | ~ r1_tarski(k2_relat_1(A_78),k1_relat_1(B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_420,plain,(
    ! [A_94,B_95] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_94),B_95)) = k1_relat_1(k2_funct_1(A_94))
      | ~ r1_tarski(k1_relat_1(A_94),k1_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k2_funct_1(A_94))
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_277])).

tff(c_438,plain,(
    ! [A_96] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_96),A_96)) = k1_relat_1(k2_funct_1(A_96))
      | ~ v1_relat_1(k2_funct_1(A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_65,c_420])).

tff(c_14,plain,(
    ! [C_13,B_11,A_10] :
      ( k1_funct_1(k5_relat_1(C_13,B_11),A_10) = k1_funct_1(B_11,k1_funct_1(C_13,A_10))
      | ~ r2_hidden(A_10,k1_relat_1(k5_relat_1(C_13,B_11)))
      | ~ v1_funct_1(C_13)
      | ~ v1_relat_1(C_13)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1293,plain,(
    ! [A_165,A_166] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(A_165),A_165),A_166) = k1_funct_1(A_165,k1_funct_1(k2_funct_1(A_165),A_166))
      | ~ r2_hidden(A_166,k1_relat_1(k2_funct_1(A_165)))
      | ~ v1_funct_1(k2_funct_1(A_165))
      | ~ v1_relat_1(k2_funct_1(A_165))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165)
      | ~ v1_relat_1(k2_funct_1(A_165))
      | ~ v2_funct_1(A_165)
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_14])).

tff(c_1754,plain,(
    ! [A_213,A_214] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(A_213),A_213),A_214) = k1_funct_1(A_213,k1_funct_1(k2_funct_1(A_213),A_214))
      | ~ r2_hidden(A_214,k2_relat_1(A_213))
      | ~ v1_funct_1(k2_funct_1(A_213))
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213)
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213)
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1293])).

tff(c_226,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),'#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1814,plain,
    ( k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6'
    | ~ r2_hidden('#skF_6',k2_relat_1('#skF_7'))
    | ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_funct_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_226])).

tff(c_1857,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_56,c_54,c_52,c_56,c_54,c_50,c_227,c_1814])).

tff(c_1862,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1857])).

tff(c_1865,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_1862])).

tff(c_1869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1865])).

tff(c_1870,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1857])).

tff(c_1874,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_1870])).

tff(c_1878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:04:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.18  
% 6.09/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.18  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 6.09/2.18  
% 6.09/2.18  %Foreground sorts:
% 6.09/2.18  
% 6.09/2.18  
% 6.09/2.18  %Background operators:
% 6.09/2.18  
% 6.09/2.18  
% 6.09/2.18  %Foreground operators:
% 6.09/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.09/2.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.09/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.09/2.18  tff('#skF_7', type, '#skF_7': $i).
% 6.09/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.09/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.09/2.18  tff('#skF_6', type, '#skF_6': $i).
% 6.09/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.09/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.09/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.09/2.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.09/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.09/2.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.09/2.18  
% 6.16/2.20  tff(f_117, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 6.16/2.20  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.16/2.20  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 6.16/2.20  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.16/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.16/2.20  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 6.16/2.20  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 6.16/2.20  tff(c_56, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.16/2.20  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.16/2.20  tff(c_10, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.16/2.20  tff(c_12, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.16/2.20  tff(c_52, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.16/2.20  tff(c_50, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.16/2.20  tff(c_155, plain, (![A_60, C_61]: (k1_funct_1(A_60, k1_funct_1(k2_funct_1(A_60), C_61))=C_61 | ~r2_hidden(C_61, k2_relat_1(A_60)) | ~v1_funct_1(k2_funct_1(A_60)) | ~v1_relat_1(k2_funct_1(A_60)) | ~v2_funct_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_48, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), '#skF_6')!='#skF_6' | k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.16/2.20  tff(c_67, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_175, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_155, c_67])).
% 6.16/2.20  tff(c_190, plain, (~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_175])).
% 6.16/2.20  tff(c_193, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_190])).
% 6.16/2.20  tff(c_196, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_193])).
% 6.16/2.20  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_196])).
% 6.16/2.20  tff(c_201, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_190])).
% 6.16/2.20  tff(c_221, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_201])).
% 6.16/2.20  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_221])).
% 6.16/2.20  tff(c_227, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_46, plain, (![A_31]: (k1_relat_1(k2_funct_1(A_31))=k2_relat_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.16/2.20  tff(c_60, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.20  tff(c_65, plain, (![A_36]: (r1_tarski(A_36, A_36))), inference(resolution, [status(thm)], [c_60, c_4])).
% 6.16/2.20  tff(c_44, plain, (![A_31]: (k2_relat_1(k2_funct_1(A_31))=k1_relat_1(A_31) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.16/2.20  tff(c_277, plain, (![A_78, B_79]: (k1_relat_1(k5_relat_1(A_78, B_79))=k1_relat_1(A_78) | ~r1_tarski(k2_relat_1(A_78), k1_relat_1(B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.16/2.20  tff(c_420, plain, (![A_94, B_95]: (k1_relat_1(k5_relat_1(k2_funct_1(A_94), B_95))=k1_relat_1(k2_funct_1(A_94)) | ~r1_tarski(k1_relat_1(A_94), k1_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(k2_funct_1(A_94)) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_44, c_277])).
% 6.16/2.20  tff(c_438, plain, (![A_96]: (k1_relat_1(k5_relat_1(k2_funct_1(A_96), A_96))=k1_relat_1(k2_funct_1(A_96)) | ~v1_relat_1(k2_funct_1(A_96)) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_65, c_420])).
% 6.16/2.20  tff(c_14, plain, (![C_13, B_11, A_10]: (k1_funct_1(k5_relat_1(C_13, B_11), A_10)=k1_funct_1(B_11, k1_funct_1(C_13, A_10)) | ~r2_hidden(A_10, k1_relat_1(k5_relat_1(C_13, B_11))) | ~v1_funct_1(C_13) | ~v1_relat_1(C_13) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.16/2.20  tff(c_1293, plain, (![A_165, A_166]: (k1_funct_1(k5_relat_1(k2_funct_1(A_165), A_165), A_166)=k1_funct_1(A_165, k1_funct_1(k2_funct_1(A_165), A_166)) | ~r2_hidden(A_166, k1_relat_1(k2_funct_1(A_165))) | ~v1_funct_1(k2_funct_1(A_165)) | ~v1_relat_1(k2_funct_1(A_165)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165) | ~v1_relat_1(k2_funct_1(A_165)) | ~v2_funct_1(A_165) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(superposition, [status(thm), theory('equality')], [c_438, c_14])).
% 6.16/2.20  tff(c_1754, plain, (![A_213, A_214]: (k1_funct_1(k5_relat_1(k2_funct_1(A_213), A_213), A_214)=k1_funct_1(A_213, k1_funct_1(k2_funct_1(A_213), A_214)) | ~r2_hidden(A_214, k2_relat_1(A_213)) | ~v1_funct_1(k2_funct_1(A_213)) | ~v1_relat_1(k2_funct_1(A_213)) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213) | ~v1_relat_1(k2_funct_1(A_213)) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1293])).
% 6.16/2.20  tff(c_226, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_1814, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6' | ~r2_hidden('#skF_6', k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1754, c_226])).
% 6.16/2.20  tff(c_1857, plain, (~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_56, c_54, c_52, c_56, c_54, c_50, c_227, c_1814])).
% 6.16/2.20  tff(c_1862, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1857])).
% 6.16/2.20  tff(c_1865, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12, c_1862])).
% 6.16/2.20  tff(c_1869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1865])).
% 6.16/2.20  tff(c_1870, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1857])).
% 6.16/2.20  tff(c_1874, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_1870])).
% 6.16/2.20  tff(c_1878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1874])).
% 6.16/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.20  
% 6.16/2.20  Inference rules
% 6.16/2.20  ----------------------
% 6.16/2.20  #Ref     : 0
% 6.16/2.20  #Sup     : 473
% 6.16/2.20  #Fact    : 0
% 6.16/2.20  #Define  : 0
% 6.16/2.20  #Split   : 3
% 6.16/2.20  #Chain   : 0
% 6.16/2.20  #Close   : 0
% 6.16/2.20  
% 6.16/2.20  Ordering : KBO
% 6.16/2.20  
% 6.16/2.20  Simplification rules
% 6.16/2.20  ----------------------
% 6.16/2.20  #Subsume      : 18
% 6.16/2.20  #Demod        : 44
% 6.16/2.20  #Tautology    : 131
% 6.16/2.20  #SimpNegUnit  : 0
% 6.16/2.20  #BackRed      : 0
% 6.16/2.20  
% 6.16/2.20  #Partial instantiations: 0
% 6.16/2.20  #Strategies tried      : 1
% 6.16/2.20  
% 6.16/2.20  Timing (in seconds)
% 6.16/2.20  ----------------------
% 6.16/2.20  Preprocessing        : 0.37
% 6.16/2.20  Parsing              : 0.18
% 6.16/2.20  CNF conversion       : 0.03
% 6.16/2.20  Main loop            : 1.05
% 6.16/2.20  Inferencing          : 0.38
% 6.16/2.20  Reduction            : 0.25
% 6.16/2.20  Demodulation         : 0.17
% 6.16/2.20  BG Simplification    : 0.07
% 6.16/2.20  Subsumption          : 0.28
% 6.16/2.20  Abstraction          : 0.07
% 6.16/2.20  MUC search           : 0.00
% 6.16/2.20  Cooper               : 0.00
% 6.16/2.20  Total                : 1.45
% 6.16/2.20  Index Insertion      : 0.00
% 6.16/2.20  Index Deletion       : 0.00
% 6.16/2.20  Index Matching       : 0.00
% 6.16/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
