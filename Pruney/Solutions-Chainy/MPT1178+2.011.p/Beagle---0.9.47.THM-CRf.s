%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 224 expanded)
%              Number of leaves         :   38 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  155 ( 672 expanded)
%              Number of equality atoms :   14 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v4_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v5_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_152,plain,(
    ! [A_82,B_83] :
      ( m2_orders_2('#skF_6'(A_82,B_83),A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_154,plain,
    ( m2_orders_2('#skF_6'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | ~ l1_orders_2('#skF_7')
    | ~ v5_orders_2('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | ~ v3_orders_2('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_152])).

tff(c_157,plain,
    ( m2_orders_2('#skF_6'('#skF_7','#skF_8'),'#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_154])).

tff(c_158,plain,(
    m2_orders_2('#skF_6'('#skF_7','#skF_8'),'#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_157])).

tff(c_379,plain,(
    ! [D_102,A_103,B_104] :
      ( r2_hidden(D_102,k4_orders_2(A_103,B_104))
      | ~ m2_orders_2(D_102,A_103,B_104)
      | ~ m1_orders_1(B_104,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_381,plain,(
    ! [D_102] :
      ( r2_hidden(D_102,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_102,'#skF_7','#skF_8')
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_379])).

tff(c_384,plain,(
    ! [D_102] :
      ( r2_hidden(D_102,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_102,'#skF_7','#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_381])).

tff(c_386,plain,(
    ! [D_105] :
      ( r2_hidden(D_105,k4_orders_2('#skF_7','#skF_8'))
      | ~ m2_orders_2(D_105,'#skF_7','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_384])).

tff(c_58,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_22,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    ! [A_13] : r1_tarski('#skF_2',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_42,plain,(
    k3_tarski(k4_orders_2('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_77,plain,(
    k3_tarski(k4_orders_2('#skF_7','#skF_8')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [B_84,A_85] :
      ( k3_tarski(B_84) = A_85
      | ~ r1_tarski(k3_tarski(B_84),A_85)
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_166,plain,(
    ! [A_85] :
      ( k3_tarski(k4_orders_2('#skF_7','#skF_8')) = A_85
      | ~ r1_tarski('#skF_2',A_85)
      | ~ r2_hidden(A_85,k4_orders_2('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_159])).

tff(c_173,plain,(
    ! [A_85] :
      ( A_85 = '#skF_2'
      | ~ r2_hidden(A_85,k4_orders_2('#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77,c_166])).

tff(c_399,plain,(
    ! [D_106] :
      ( D_106 = '#skF_2'
      | ~ m2_orders_2(D_106,'#skF_7','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_386,c_173])).

tff(c_403,plain,(
    '#skF_6'('#skF_7','#skF_8') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_158,c_399])).

tff(c_404,plain,(
    m2_orders_2('#skF_2','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_158])).

tff(c_123,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_3'(A_71,B_72),A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_577,plain,(
    ! [C_122,D_123,A_124,B_125] :
      ( ~ r1_xboole_0(C_122,D_123)
      | ~ m2_orders_2(D_123,A_124,B_125)
      | ~ m2_orders_2(C_122,A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_997,plain,(
    ! [B_165,A_166,B_167,A_168] :
      ( ~ m2_orders_2(B_165,A_166,B_167)
      | ~ m2_orders_2(A_168,A_166,B_167)
      | ~ m1_orders_1(B_167,k1_orders_1(u1_struct_0(A_166)))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166)
      | ~ v4_orders_2(A_166)
      | ~ v3_orders_2(A_166)
      | v2_struct_0(A_166)
      | ~ v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_132,c_577])).

tff(c_999,plain,(
    ! [A_168] :
      ( ~ m2_orders_2(A_168,'#skF_7','#skF_8')
      | ~ m1_orders_1('#skF_8',k1_orders_1(u1_struct_0('#skF_7')))
      | ~ l1_orders_2('#skF_7')
      | ~ v5_orders_2('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | ~ v3_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_404,c_997])).

tff(c_1002,plain,(
    ! [A_168] :
      ( ~ m2_orders_2(A_168,'#skF_7','#skF_8')
      | v2_struct_0('#skF_7')
      | ~ v1_xboole_0(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_999])).

tff(c_1004,plain,(
    ! [A_169] :
      ( ~ m2_orders_2(A_169,'#skF_7','#skF_8')
      | ~ v1_xboole_0(A_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1002])).

tff(c_1007,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_404,c_1004])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.86/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.86/1.45  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.86/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.45  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.86/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.86/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.45  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.86/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.86/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.86/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.86/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.86/1.45  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.86/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.45  
% 3.21/1.47  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 3.21/1.47  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 3.21/1.47  tff(f_105, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 3.21/1.47  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 3.21/1.47  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.21/1.47  tff(f_63, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.47  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.21/1.47  tff(f_61, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.47  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.21/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.47  tff(f_128, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 3.21/1.47  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.47  tff(c_54, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_52, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_50, plain, (v4_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_48, plain, (v5_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_46, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_44, plain, (m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_152, plain, (![A_82, B_83]: (m2_orders_2('#skF_6'(A_82, B_83), A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.21/1.47  tff(c_154, plain, (m2_orders_2('#skF_6'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_44, c_152])).
% 3.21/1.47  tff(c_157, plain, (m2_orders_2('#skF_6'('#skF_7', '#skF_8'), '#skF_7', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_154])).
% 3.21/1.47  tff(c_158, plain, (m2_orders_2('#skF_6'('#skF_7', '#skF_8'), '#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_157])).
% 3.21/1.47  tff(c_379, plain, (![D_102, A_103, B_104]: (r2_hidden(D_102, k4_orders_2(A_103, B_104)) | ~m2_orders_2(D_102, A_103, B_104) | ~m1_orders_1(B_104, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.21/1.47  tff(c_381, plain, (![D_102]: (r2_hidden(D_102, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_102, '#skF_7', '#skF_8') | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_379])).
% 3.21/1.47  tff(c_384, plain, (![D_102]: (r2_hidden(D_102, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_102, '#skF_7', '#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_381])).
% 3.21/1.47  tff(c_386, plain, (![D_105]: (r2_hidden(D_105, k4_orders_2('#skF_7', '#skF_8')) | ~m2_orders_2(D_105, '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_54, c_384])).
% 3.21/1.47  tff(c_58, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.47  tff(c_62, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_58])).
% 3.21/1.47  tff(c_22, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.21/1.47  tff(c_64, plain, (![A_13]: (r1_tarski('#skF_2', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 3.21/1.47  tff(c_42, plain, (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.21/1.47  tff(c_77, plain, (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42])).
% 3.21/1.47  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.21/1.47  tff(c_91, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.21/1.47  tff(c_159, plain, (![B_84, A_85]: (k3_tarski(B_84)=A_85 | ~r1_tarski(k3_tarski(B_84), A_85) | ~r2_hidden(A_85, B_84))), inference(resolution, [status(thm)], [c_24, c_91])).
% 3.21/1.47  tff(c_166, plain, (![A_85]: (k3_tarski(k4_orders_2('#skF_7', '#skF_8'))=A_85 | ~r1_tarski('#skF_2', A_85) | ~r2_hidden(A_85, k4_orders_2('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_77, c_159])).
% 3.21/1.47  tff(c_173, plain, (![A_85]: (A_85='#skF_2' | ~r2_hidden(A_85, k4_orders_2('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_77, c_166])).
% 3.21/1.47  tff(c_399, plain, (![D_106]: (D_106='#skF_2' | ~m2_orders_2(D_106, '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_386, c_173])).
% 3.21/1.47  tff(c_403, plain, ('#skF_6'('#skF_7', '#skF_8')='#skF_2'), inference(resolution, [status(thm)], [c_158, c_399])).
% 3.21/1.47  tff(c_404, plain, (m2_orders_2('#skF_2', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_158])).
% 3.21/1.47  tff(c_123, plain, (![A_71, B_72]: (r2_hidden('#skF_3'(A_71, B_72), A_71) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.47  tff(c_132, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r1_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.21/1.47  tff(c_577, plain, (![C_122, D_123, A_124, B_125]: (~r1_xboole_0(C_122, D_123) | ~m2_orders_2(D_123, A_124, B_125) | ~m2_orders_2(C_122, A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.21/1.47  tff(c_997, plain, (![B_165, A_166, B_167, A_168]: (~m2_orders_2(B_165, A_166, B_167) | ~m2_orders_2(A_168, A_166, B_167) | ~m1_orders_1(B_167, k1_orders_1(u1_struct_0(A_166))) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166) | ~v4_orders_2(A_166) | ~v3_orders_2(A_166) | v2_struct_0(A_166) | ~v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_132, c_577])).
% 3.21/1.47  tff(c_999, plain, (![A_168]: (~m2_orders_2(A_168, '#skF_7', '#skF_8') | ~m1_orders_1('#skF_8', k1_orders_1(u1_struct_0('#skF_7'))) | ~l1_orders_2('#skF_7') | ~v5_orders_2('#skF_7') | ~v4_orders_2('#skF_7') | ~v3_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_404, c_997])).
% 3.21/1.47  tff(c_1002, plain, (![A_168]: (~m2_orders_2(A_168, '#skF_7', '#skF_8') | v2_struct_0('#skF_7') | ~v1_xboole_0(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_999])).
% 3.21/1.47  tff(c_1004, plain, (![A_169]: (~m2_orders_2(A_169, '#skF_7', '#skF_8') | ~v1_xboole_0(A_169))), inference(negUnitSimplification, [status(thm)], [c_54, c_1002])).
% 3.21/1.47  tff(c_1007, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_404, c_1004])).
% 3.21/1.47  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1007])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 200
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 1
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 45
% 3.21/1.47  #Demod        : 150
% 3.21/1.47  #Tautology    : 87
% 3.21/1.47  #SimpNegUnit  : 15
% 3.21/1.47  #BackRed      : 8
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.47  Preprocessing        : 0.31
% 3.21/1.47  Parsing              : 0.17
% 3.21/1.47  CNF conversion       : 0.03
% 3.21/1.47  Main loop            : 0.39
% 3.21/1.47  Inferencing          : 0.15
% 3.21/1.47  Reduction            : 0.12
% 3.21/1.47  Demodulation         : 0.08
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.08
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.74
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
