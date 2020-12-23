%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:03 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 224 expanded)
%              Number of leaves         :   36 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 ( 541 expanded)
%              Number of equality atoms :   17 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_106,axiom,(
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
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [A_61,B_62] :
      ( m2_orders_2('#skF_5'(A_61,B_62),A_61,B_62)
      | ~ m1_orders_1(B_62,k1_orders_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_156,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_159,plain,
    ( m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_156])).

tff(c_160,plain,(
    m2_orders_2('#skF_5'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_159])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_71,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_36])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,k3_tarski(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [B_58,A_59] :
      ( k3_tarski(B_58) = A_59
      | ~ r1_tarski(k3_tarski(B_58),A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_124,plain,(
    ! [A_59] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) = A_59
      | ~ r1_tarski('#skF_2',A_59)
      | ~ r2_hidden(A_59,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_117])).

tff(c_134,plain,(
    ! [A_60] :
      ( A_60 = '#skF_2'
      | ~ r2_hidden(A_60,k4_orders_2('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_71,c_124])).

tff(c_139,plain,
    ( '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = '#skF_2'
    | v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_140,plain,(
    v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_144,plain,(
    k4_orders_2('#skF_6','#skF_7') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_140,c_57])).

tff(c_202,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,k4_orders_2(A_71,B_72))
      | ~ m2_orders_2(D_70,A_71,B_72)
      | ~ m1_orders_1(B_72,k1_orders_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | ~ v5_orders_2(A_71)
      | ~ v4_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_204,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_70,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_207,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,'#skF_2')
      | ~ m2_orders_2(D_70,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_144,c_204])).

tff(c_209,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,'#skF_2')
      | ~ m2_orders_2(D_73,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_207])).

tff(c_213,plain,(
    r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_209])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_222])).

tff(c_230,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_229,plain,(
    '#skF_1'(k4_orders_2('#skF_6','#skF_7')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_246,plain,
    ( v1_xboole_0(k4_orders_2('#skF_6','#skF_7'))
    | r2_hidden('#skF_2',k4_orders_2('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_4])).

tff(c_249,plain,(
    r2_hidden('#skF_2',k4_orders_2('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_246])).

tff(c_278,plain,(
    ! [D_78,A_79,B_80] :
      ( m2_orders_2(D_78,A_79,B_80)
      | ~ r2_hidden(D_78,k4_orders_2(A_79,B_80))
      | ~ m1_orders_1(B_80,k1_orders_1(u1_struct_0(A_79)))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_280,plain,
    ( m2_orders_2('#skF_2','#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_249,c_278])).

tff(c_286,plain,
    ( m2_orders_2('#skF_2','#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_280])).

tff(c_287,plain,(
    m2_orders_2('#skF_2','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_286])).

tff(c_342,plain,(
    ! [B_87,A_88,C_89] :
      ( r2_hidden(k1_funct_1(B_87,u1_struct_0(A_88)),C_89)
      | ~ m2_orders_2(C_89,A_88,B_87)
      | ~ m1_orders_1(B_87,k1_orders_1(u1_struct_0(A_88)))
      | ~ l1_orders_2(A_88)
      | ~ v5_orders_2(A_88)
      | ~ v4_orders_2(A_88)
      | ~ v3_orders_2(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_361,plain,(
    ! [C_90,A_91,B_92] :
      ( ~ v1_xboole_0(C_90)
      | ~ m2_orders_2(C_90,A_91,B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_342,c_2])).

tff(c_363,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_287,c_361])).

tff(c_366,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_8,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.29  
% 2.36/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5
% 2.36/1.30  
% 2.36/1.30  %Foreground sorts:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Background operators:
% 2.36/1.30  
% 2.36/1.30  
% 2.36/1.30  %Foreground operators:
% 2.36/1.30  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.36/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.30  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.36/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.36/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.30  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.36/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.36/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.36/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.36/1.30  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.36/1.30  
% 2.36/1.31  tff(f_124, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.36/1.31  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.36/1.31  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.36/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.36/1.31  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.31  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.36/1.31  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.36/1.31  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.31  tff(f_71, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.36/1.31  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.36/1.31  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_46, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_44, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_42, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_40, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_38, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.31  tff(c_154, plain, (![A_61, B_62]: (m2_orders_2('#skF_5'(A_61, B_62), A_61, B_62) | ~m1_orders_1(B_62, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.36/1.31  tff(c_156, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_154])).
% 2.36/1.31  tff(c_159, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_156])).
% 2.36/1.31  tff(c_160, plain, (m2_orders_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_48, c_159])).
% 2.36/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.31  tff(c_52, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.31  tff(c_56, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_52])).
% 2.36/1.31  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.31  tff(c_58, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 2.36/1.31  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.36/1.31  tff(c_71, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_36])).
% 2.36/1.31  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, k3_tarski(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.31  tff(c_85, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.31  tff(c_117, plain, (![B_58, A_59]: (k3_tarski(B_58)=A_59 | ~r1_tarski(k3_tarski(B_58), A_59) | ~r2_hidden(A_59, B_58))), inference(resolution, [status(thm)], [c_18, c_85])).
% 2.36/1.31  tff(c_124, plain, (![A_59]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=A_59 | ~r1_tarski('#skF_2', A_59) | ~r2_hidden(A_59, k4_orders_2('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_117])).
% 2.36/1.31  tff(c_134, plain, (![A_60]: (A_60='#skF_2' | ~r2_hidden(A_60, k4_orders_2('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_71, c_124])).
% 2.36/1.31  tff(c_139, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))='#skF_2' | v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_134])).
% 2.36/1.31  tff(c_140, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.36/1.31  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.31  tff(c_57, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 2.36/1.31  tff(c_144, plain, (k4_orders_2('#skF_6', '#skF_7')='#skF_2'), inference(resolution, [status(thm)], [c_140, c_57])).
% 2.36/1.31  tff(c_202, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, k4_orders_2(A_71, B_72)) | ~m2_orders_2(D_70, A_71, B_72) | ~m1_orders_1(B_72, k1_orders_1(u1_struct_0(A_71))) | ~l1_orders_2(A_71) | ~v5_orders_2(A_71) | ~v4_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.31  tff(c_204, plain, (![D_70]: (r2_hidden(D_70, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_70, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_38, c_202])).
% 2.36/1.31  tff(c_207, plain, (![D_70]: (r2_hidden(D_70, '#skF_2') | ~m2_orders_2(D_70, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_144, c_204])).
% 2.36/1.31  tff(c_209, plain, (![D_73]: (r2_hidden(D_73, '#skF_2') | ~m2_orders_2(D_73, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_48, c_207])).
% 2.36/1.31  tff(c_213, plain, (r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_2')), inference(resolution, [status(thm)], [c_160, c_209])).
% 2.36/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.31  tff(c_222, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_213, c_2])).
% 2.36/1.31  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_222])).
% 2.36/1.31  tff(c_230, plain, (~v1_xboole_0(k4_orders_2('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_139])).
% 2.36/1.31  tff(c_229, plain, ('#skF_1'(k4_orders_2('#skF_6', '#skF_7'))='#skF_2'), inference(splitRight, [status(thm)], [c_139])).
% 2.36/1.31  tff(c_246, plain, (v1_xboole_0(k4_orders_2('#skF_6', '#skF_7')) | r2_hidden('#skF_2', k4_orders_2('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_4])).
% 2.36/1.31  tff(c_249, plain, (r2_hidden('#skF_2', k4_orders_2('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_230, c_246])).
% 2.36/1.31  tff(c_278, plain, (![D_78, A_79, B_80]: (m2_orders_2(D_78, A_79, B_80) | ~r2_hidden(D_78, k4_orders_2(A_79, B_80)) | ~m1_orders_1(B_80, k1_orders_1(u1_struct_0(A_79))) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.31  tff(c_280, plain, (m2_orders_2('#skF_2', '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_249, c_278])).
% 2.36/1.31  tff(c_286, plain, (m2_orders_2('#skF_2', '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_280])).
% 2.36/1.31  tff(c_287, plain, (m2_orders_2('#skF_2', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_48, c_286])).
% 2.36/1.31  tff(c_342, plain, (![B_87, A_88, C_89]: (r2_hidden(k1_funct_1(B_87, u1_struct_0(A_88)), C_89) | ~m2_orders_2(C_89, A_88, B_87) | ~m1_orders_1(B_87, k1_orders_1(u1_struct_0(A_88))) | ~l1_orders_2(A_88) | ~v5_orders_2(A_88) | ~v4_orders_2(A_88) | ~v3_orders_2(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.36/1.31  tff(c_361, plain, (![C_90, A_91, B_92]: (~v1_xboole_0(C_90) | ~m2_orders_2(C_90, A_91, B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_342, c_2])).
% 2.36/1.31  tff(c_363, plain, (~v1_xboole_0('#skF_2') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_287, c_361])).
% 2.36/1.31  tff(c_366, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_8, c_363])).
% 2.36/1.31  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_366])).
% 2.36/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  Inference rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Ref     : 0
% 2.36/1.31  #Sup     : 64
% 2.36/1.31  #Fact    : 0
% 2.36/1.31  #Define  : 0
% 2.36/1.31  #Split   : 1
% 2.36/1.31  #Chain   : 0
% 2.36/1.31  #Close   : 0
% 2.36/1.31  
% 2.36/1.31  Ordering : KBO
% 2.36/1.31  
% 2.36/1.31  Simplification rules
% 2.36/1.31  ----------------------
% 2.36/1.31  #Subsume      : 7
% 2.36/1.31  #Demod        : 71
% 2.36/1.31  #Tautology    : 32
% 2.36/1.31  #SimpNegUnit  : 10
% 2.36/1.31  #BackRed      : 8
% 2.36/1.31  
% 2.36/1.31  #Partial instantiations: 0
% 2.36/1.31  #Strategies tried      : 1
% 2.36/1.31  
% 2.36/1.31  Timing (in seconds)
% 2.36/1.31  ----------------------
% 2.54/1.32  Preprocessing        : 0.31
% 2.54/1.32  Parsing              : 0.17
% 2.54/1.32  CNF conversion       : 0.03
% 2.54/1.32  Main loop            : 0.24
% 2.54/1.32  Inferencing          : 0.09
% 2.54/1.32  Reduction            : 0.07
% 2.54/1.32  Demodulation         : 0.05
% 2.54/1.32  BG Simplification    : 0.01
% 2.54/1.32  Subsumption          : 0.04
% 2.54/1.32  Abstraction          : 0.01
% 2.54/1.32  MUC search           : 0.00
% 2.54/1.32  Cooper               : 0.00
% 2.54/1.32  Total                : 0.58
% 2.54/1.32  Index Insertion      : 0.00
% 2.54/1.32  Index Deletion       : 0.00
% 2.54/1.32  Index Matching       : 0.00
% 2.54/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
