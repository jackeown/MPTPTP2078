%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   76 (  85 expanded)
%              Number of leaves         :   41 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 130 expanded)
%              Number of equality atoms :   40 (  51 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(c_88,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_80,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_5'(A_47),A_47)
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_123,plain,(
    ! [D_69,A_70,B_71] :
      ( r2_hidden(D_69,A_70)
      | ~ r2_hidden(D_69,k4_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_137,B_138)),A_137)
      | k4_xboole_0(A_137,B_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_123])).

tff(c_117,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_68,B_67] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_68,B_67)),B_67)
      | k4_xboole_0(A_68,B_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_117])).

tff(c_286,plain,(
    ! [A_137] : k4_xboole_0(A_137,A_137) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_122])).

tff(c_34,plain,(
    ! [B_36] : k4_xboole_0(k1_tarski(B_36),k1_tarski(B_36)) != k1_tarski(B_36) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_292,plain,(
    ! [B_36] : k1_tarski(B_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_34])).

tff(c_96,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_94,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_92,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_90,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_841,plain,(
    ! [D_245,C_246,B_247,A_248] :
      ( r2_hidden(k1_funct_1(D_245,C_246),B_247)
      | k1_xboole_0 = B_247
      | ~ r2_hidden(C_246,A_248)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247)))
      | ~ v1_funct_2(D_245,A_248,B_247)
      | ~ v1_funct_1(D_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1030,plain,(
    ! [D_255,B_256] :
      ( r2_hidden(k1_funct_1(D_255,'#skF_8'),B_256)
      | k1_xboole_0 = B_256
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_256)))
      | ~ v1_funct_2(D_255,'#skF_6',B_256)
      | ~ v1_funct_1(D_255) ) ),
    inference(resolution,[status(thm)],[c_90,c_841])).

tff(c_1033,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_1030])).

tff(c_1036,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7'))
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_1033])).

tff(c_1037,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_8'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_1036])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_338,plain,(
    ! [C_143,A_144,E_147,D_146,B_145] : k4_enumset1(A_144,A_144,B_145,C_143,D_146,E_147) = k3_enumset1(A_144,B_145,C_143,D_146,E_147) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [B_38,H_46,A_37,D_40,F_42,E_41] : r2_hidden(H_46,k4_enumset1(A_37,B_38,H_46,D_40,E_41,F_42)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_452,plain,(
    ! [E_162,C_159,D_161,A_158,B_160] : r2_hidden(B_160,k3_enumset1(A_158,B_160,C_159,D_161,E_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_46])).

tff(c_462,plain,(
    ! [A_163,B_164,C_165,D_166] : r2_hidden(A_163,k2_enumset1(A_163,B_164,C_165,D_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_452])).

tff(c_478,plain,(
    ! [A_170,B_171,C_172] : r2_hidden(A_170,k1_enumset1(A_170,B_171,C_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_462])).

tff(c_488,plain,(
    ! [A_173,B_174] : r2_hidden(A_173,k2_tarski(A_173,B_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_478])).

tff(c_498,plain,(
    ! [A_175] : r2_hidden(A_175,k1_tarski(A_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_488])).

tff(c_144,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(k1_tarski(A_105),k1_tarski(B_106)) = k1_tarski(A_105)
      | B_106 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [D_6,B_106,A_105] :
      ( ~ r2_hidden(D_6,k1_tarski(B_106))
      | ~ r2_hidden(D_6,k1_tarski(A_105))
      | B_106 = A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_505,plain,(
    ! [A_175,A_105] :
      ( ~ r2_hidden(A_175,k1_tarski(A_105))
      | A_175 = A_105 ) ),
    inference(resolution,[status(thm)],[c_498,c_153])).

tff(c_1042,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1037,c_505])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.55  
% 3.88/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.56  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 3.88/1.56  
% 3.88/1.56  %Foreground sorts:
% 3.88/1.56  
% 3.88/1.56  
% 3.88/1.56  %Background operators:
% 3.88/1.56  
% 3.88/1.56  
% 3.88/1.56  %Foreground operators:
% 3.88/1.56  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.88/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.88/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.88/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.88/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.88/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.88/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.88/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.88/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.88/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.88/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.88/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.88/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.56  
% 3.88/1.58  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.88/1.58  tff(f_94, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.88/1.58  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.88/1.58  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.88/1.58  tff(f_106, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.88/1.58  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.88/1.58  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.88/1.58  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.88/1.58  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.88/1.58  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.88/1.58  tff(f_78, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 3.88/1.58  tff(c_88, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.58  tff(c_80, plain, (![A_47]: (r2_hidden('#skF_5'(A_47), A_47) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.88/1.58  tff(c_123, plain, (![D_69, A_70, B_71]: (r2_hidden(D_69, A_70) | ~r2_hidden(D_69, k4_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.58  tff(c_263, plain, (![A_137, B_138]: (r2_hidden('#skF_5'(k4_xboole_0(A_137, B_138)), A_137) | k4_xboole_0(A_137, B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_123])).
% 3.88/1.58  tff(c_117, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.58  tff(c_122, plain, (![A_68, B_67]: (~r2_hidden('#skF_5'(k4_xboole_0(A_68, B_67)), B_67) | k4_xboole_0(A_68, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_117])).
% 3.88/1.58  tff(c_286, plain, (![A_137]: (k4_xboole_0(A_137, A_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_263, c_122])).
% 3.88/1.58  tff(c_34, plain, (![B_36]: (k4_xboole_0(k1_tarski(B_36), k1_tarski(B_36))!=k1_tarski(B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/1.58  tff(c_292, plain, (![B_36]: (k1_tarski(B_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_34])).
% 3.88/1.58  tff(c_96, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.58  tff(c_94, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.58  tff(c_92, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.58  tff(c_90, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.58  tff(c_841, plain, (![D_245, C_246, B_247, A_248]: (r2_hidden(k1_funct_1(D_245, C_246), B_247) | k1_xboole_0=B_247 | ~r2_hidden(C_246, A_248) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))) | ~v1_funct_2(D_245, A_248, B_247) | ~v1_funct_1(D_245))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.88/1.58  tff(c_1030, plain, (![D_255, B_256]: (r2_hidden(k1_funct_1(D_255, '#skF_8'), B_256) | k1_xboole_0=B_256 | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_256))) | ~v1_funct_2(D_255, '#skF_6', B_256) | ~v1_funct_1(D_255))), inference(resolution, [status(thm)], [c_90, c_841])).
% 3.88/1.58  tff(c_1033, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_92, c_1030])).
% 3.88/1.58  tff(c_1036, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7')) | k1_tarski('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_1033])).
% 3.88/1.58  tff(c_1037, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_8'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_292, c_1036])).
% 3.88/1.58  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.58  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.58  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.88/1.58  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.58  tff(c_338, plain, (![C_143, A_144, E_147, D_146, B_145]: (k4_enumset1(A_144, A_144, B_145, C_143, D_146, E_147)=k3_enumset1(A_144, B_145, C_143, D_146, E_147))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.88/1.58  tff(c_46, plain, (![B_38, H_46, A_37, D_40, F_42, E_41]: (r2_hidden(H_46, k4_enumset1(A_37, B_38, H_46, D_40, E_41, F_42)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.88/1.58  tff(c_452, plain, (![E_162, C_159, D_161, A_158, B_160]: (r2_hidden(B_160, k3_enumset1(A_158, B_160, C_159, D_161, E_162)))), inference(superposition, [status(thm), theory('equality')], [c_338, c_46])).
% 3.88/1.58  tff(c_462, plain, (![A_163, B_164, C_165, D_166]: (r2_hidden(A_163, k2_enumset1(A_163, B_164, C_165, D_166)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_452])).
% 3.88/1.58  tff(c_478, plain, (![A_170, B_171, C_172]: (r2_hidden(A_170, k1_enumset1(A_170, B_171, C_172)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_462])).
% 3.88/1.58  tff(c_488, plain, (![A_173, B_174]: (r2_hidden(A_173, k2_tarski(A_173, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_478])).
% 3.88/1.58  tff(c_498, plain, (![A_175]: (r2_hidden(A_175, k1_tarski(A_175)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_488])).
% 3.88/1.58  tff(c_144, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), k1_tarski(B_106))=k1_tarski(A_105) | B_106=A_105)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/1.58  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.58  tff(c_153, plain, (![D_6, B_106, A_105]: (~r2_hidden(D_6, k1_tarski(B_106)) | ~r2_hidden(D_6, k1_tarski(A_105)) | B_106=A_105)), inference(superposition, [status(thm), theory('equality')], [c_144, c_4])).
% 3.88/1.58  tff(c_505, plain, (![A_175, A_105]: (~r2_hidden(A_175, k1_tarski(A_105)) | A_175=A_105)), inference(resolution, [status(thm)], [c_498, c_153])).
% 3.88/1.58  tff(c_1042, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_1037, c_505])).
% 3.88/1.58  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1042])).
% 3.88/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.58  
% 3.88/1.58  Inference rules
% 3.88/1.58  ----------------------
% 3.88/1.58  #Ref     : 0
% 3.88/1.58  #Sup     : 234
% 3.88/1.58  #Fact    : 0
% 3.88/1.58  #Define  : 0
% 3.88/1.58  #Split   : 2
% 3.88/1.58  #Chain   : 0
% 3.88/1.58  #Close   : 0
% 3.88/1.58  
% 3.88/1.58  Ordering : KBO
% 3.88/1.58  
% 3.88/1.58  Simplification rules
% 3.88/1.58  ----------------------
% 3.88/1.58  #Subsume      : 17
% 3.88/1.58  #Demod        : 27
% 3.88/1.58  #Tautology    : 65
% 3.88/1.58  #SimpNegUnit  : 21
% 3.88/1.58  #BackRed      : 1
% 3.88/1.58  
% 3.88/1.58  #Partial instantiations: 0
% 3.88/1.58  #Strategies tried      : 1
% 3.88/1.58  
% 3.88/1.58  Timing (in seconds)
% 3.88/1.58  ----------------------
% 3.88/1.59  Preprocessing        : 0.38
% 3.88/1.59  Parsing              : 0.18
% 3.88/1.59  CNF conversion       : 0.03
% 3.88/1.59  Main loop            : 0.48
% 3.88/1.59  Inferencing          : 0.16
% 3.88/1.59  Reduction            : 0.14
% 3.88/1.59  Demodulation         : 0.10
% 3.88/1.59  BG Simplification    : 0.03
% 3.88/1.59  Subsumption          : 0.10
% 3.88/1.59  Abstraction          : 0.05
% 3.88/1.59  MUC search           : 0.00
% 3.88/1.59  Cooper               : 0.00
% 3.88/1.59  Total                : 0.91
% 3.88/1.59  Index Insertion      : 0.00
% 3.88/1.59  Index Deletion       : 0.00
% 3.88/1.59  Index Matching       : 0.00
% 3.88/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
