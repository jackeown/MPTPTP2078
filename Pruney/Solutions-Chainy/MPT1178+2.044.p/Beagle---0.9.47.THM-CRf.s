%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of leaves         :   32 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 ( 381 expanded)
%              Number of equality atoms :    3 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_118,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_65,axiom,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_193,plain,(
    ! [A_84,B_85] :
      ( m2_orders_2('#skF_4'(A_84,B_85),A_84,B_85)
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_195,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_198,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_195])).

tff(c_199,plain,(
    m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_198])).

tff(c_309,plain,(
    ! [D_114,A_115,B_116] :
      ( r2_hidden(D_114,k4_orders_2(A_115,B_116))
      | ~ m2_orders_2(D_114,A_115,B_116)
      | ~ m1_orders_1(B_116,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_311,plain,(
    ! [D_114] :
      ( r2_hidden(D_114,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_114,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_309])).

tff(c_314,plain,(
    ! [D_114] :
      ( r2_hidden(D_114,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_114,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_311])).

tff(c_316,plain,(
    ! [D_117] :
      ( r2_hidden(D_117,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_117,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_314])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_76,B_77,B_78,B_79] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_78)
      | ~ r1_tarski(B_79,B_78)
      | ~ r1_tarski(A_76,B_79)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_176,plain,(
    ! [A_80,B_81,B_82,A_83] :
      ( r2_hidden('#skF_1'(A_80,B_81),k3_tarski(B_82))
      | ~ r1_tarski(A_80,A_83)
      | r1_tarski(A_80,B_81)
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_160])).

tff(c_200,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_86,B_87),k3_tarski(B_88))
      | r1_tarski(A_86,B_87)
      | ~ r2_hidden(A_86,B_88) ) ),
    inference(resolution,[status(thm)],[c_62,c_176])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_216,plain,(
    ! [B_89,A_90,B_91] :
      ( ~ r1_tarski(k3_tarski(B_89),'#skF_1'(A_90,B_91))
      | r1_tarski(A_90,B_91)
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_200,c_12])).

tff(c_219,plain,(
    ! [A_90,B_91] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_90,B_91))
      | r1_tarski(A_90,B_91)
      | ~ r2_hidden(A_90,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_216])).

tff(c_221,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ r2_hidden(A_90,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_343,plain,(
    ! [D_118,B_119] :
      ( r1_tarski(D_118,B_119)
      | ~ m2_orders_2(D_118,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_316,c_221])).

tff(c_346,plain,(
    ! [B_119] : r1_tarski('#skF_4'('#skF_5','#skF_6'),B_119) ),
    inference(resolution,[status(thm)],[c_199,c_343])).

tff(c_381,plain,(
    ! [B_121,A_122,C_123] :
      ( r2_hidden(k1_funct_1(B_121,u1_struct_0(A_122)),C_123)
      | ~ m2_orders_2(C_123,A_122,B_121)
      | ~ m1_orders_1(B_121,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_537,plain,(
    ! [C_160,B_161,A_162] :
      ( ~ r1_tarski(C_160,k1_funct_1(B_161,u1_struct_0(A_162)))
      | ~ m2_orders_2(C_160,A_162,B_161)
      | ~ m1_orders_1(B_161,k1_orders_1(u1_struct_0(A_162)))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_381,c_12])).

tff(c_572,plain,(
    ! [A_167,B_168] :
      ( ~ m2_orders_2('#skF_4'('#skF_5','#skF_6'),A_167,B_168)
      | ~ m1_orders_1(B_168,k1_orders_1(u1_struct_0(A_167)))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_346,c_537])).

tff(c_575,plain,
    ( ~ m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_572])).

tff(c_578,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_199,c_575])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n024.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:35:51 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.48  
% 2.88/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.48  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.48  
% 2.88/1.48  %Foreground sorts:
% 2.88/1.48  
% 2.88/1.48  
% 2.88/1.48  %Background operators:
% 2.88/1.48  
% 2.88/1.48  
% 2.88/1.48  %Foreground operators:
% 2.88/1.48  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.88/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.88/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.48  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.88/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.48  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.88/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.88/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.88/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.88/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.88/1.48  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.88/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.88/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.88/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.88/1.48  
% 2.88/1.50  tff(f_118, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.88/1.50  tff(f_81, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.88/1.50  tff(f_65, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.88/1.50  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.88/1.50  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.88/1.50  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.88/1.50  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.88/1.50  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_40, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_38, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_36, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_34, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_32, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_193, plain, (![A_84, B_85]: (m2_orders_2('#skF_4'(A_84, B_85), A_84, B_85) | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.50  tff(c_195, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_193])).
% 2.88/1.50  tff(c_198, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_195])).
% 2.88/1.50  tff(c_199, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_198])).
% 2.88/1.50  tff(c_309, plain, (![D_114, A_115, B_116]: (r2_hidden(D_114, k4_orders_2(A_115, B_116)) | ~m2_orders_2(D_114, A_115, B_116) | ~m1_orders_1(B_116, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.88/1.50  tff(c_311, plain, (![D_114]: (r2_hidden(D_114, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_114, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_309])).
% 2.88/1.50  tff(c_314, plain, (![D_114]: (r2_hidden(D_114, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_114, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_311])).
% 2.88/1.50  tff(c_316, plain, (![D_117]: (r2_hidden(D_117, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_117, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_314])).
% 2.88/1.50  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.88/1.50  tff(c_30, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.88/1.50  tff(c_54, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.50  tff(c_62, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_54, c_4])).
% 2.88/1.50  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.50  tff(c_78, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.50  tff(c_82, plain, (![A_60, B_61, B_62]: (r2_hidden('#skF_1'(A_60, B_61), B_62) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_6, c_78])).
% 2.88/1.50  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.50  tff(c_160, plain, (![A_76, B_77, B_78, B_79]: (r2_hidden('#skF_1'(A_76, B_77), B_78) | ~r1_tarski(B_79, B_78) | ~r1_tarski(A_76, B_79) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_82, c_2])).
% 2.88/1.50  tff(c_176, plain, (![A_80, B_81, B_82, A_83]: (r2_hidden('#skF_1'(A_80, B_81), k3_tarski(B_82)) | ~r1_tarski(A_80, A_83) | r1_tarski(A_80, B_81) | ~r2_hidden(A_83, B_82))), inference(resolution, [status(thm)], [c_10, c_160])).
% 2.88/1.50  tff(c_200, plain, (![A_86, B_87, B_88]: (r2_hidden('#skF_1'(A_86, B_87), k3_tarski(B_88)) | r1_tarski(A_86, B_87) | ~r2_hidden(A_86, B_88))), inference(resolution, [status(thm)], [c_62, c_176])).
% 2.88/1.50  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.50  tff(c_216, plain, (![B_89, A_90, B_91]: (~r1_tarski(k3_tarski(B_89), '#skF_1'(A_90, B_91)) | r1_tarski(A_90, B_91) | ~r2_hidden(A_90, B_89))), inference(resolution, [status(thm)], [c_200, c_12])).
% 2.88/1.50  tff(c_219, plain, (![A_90, B_91]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_90, B_91)) | r1_tarski(A_90, B_91) | ~r2_hidden(A_90, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_216])).
% 2.88/1.50  tff(c_221, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~r2_hidden(A_90, k4_orders_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_219])).
% 2.88/1.50  tff(c_343, plain, (![D_118, B_119]: (r1_tarski(D_118, B_119) | ~m2_orders_2(D_118, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_316, c_221])).
% 2.88/1.50  tff(c_346, plain, (![B_119]: (r1_tarski('#skF_4'('#skF_5', '#skF_6'), B_119))), inference(resolution, [status(thm)], [c_199, c_343])).
% 2.88/1.50  tff(c_381, plain, (![B_121, A_122, C_123]: (r2_hidden(k1_funct_1(B_121, u1_struct_0(A_122)), C_123) | ~m2_orders_2(C_123, A_122, B_121) | ~m1_orders_1(B_121, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.88/1.50  tff(c_537, plain, (![C_160, B_161, A_162]: (~r1_tarski(C_160, k1_funct_1(B_161, u1_struct_0(A_162))) | ~m2_orders_2(C_160, A_162, B_161) | ~m1_orders_1(B_161, k1_orders_1(u1_struct_0(A_162))) | ~l1_orders_2(A_162) | ~v5_orders_2(A_162) | ~v4_orders_2(A_162) | ~v3_orders_2(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_381, c_12])).
% 2.88/1.50  tff(c_572, plain, (![A_167, B_168]: (~m2_orders_2('#skF_4'('#skF_5', '#skF_6'), A_167, B_168) | ~m1_orders_1(B_168, k1_orders_1(u1_struct_0(A_167))) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_346, c_537])).
% 2.88/1.50  tff(c_575, plain, (~m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_572])).
% 2.88/1.50  tff(c_578, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_199, c_575])).
% 2.88/1.50  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_578])).
% 2.88/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.50  
% 2.88/1.50  Inference rules
% 2.88/1.50  ----------------------
% 2.88/1.50  #Ref     : 0
% 2.88/1.50  #Sup     : 117
% 2.88/1.50  #Fact    : 0
% 2.88/1.50  #Define  : 0
% 2.88/1.50  #Split   : 1
% 2.88/1.50  #Chain   : 0
% 2.88/1.50  #Close   : 0
% 2.88/1.50  
% 2.88/1.50  Ordering : KBO
% 2.88/1.50  
% 2.88/1.50  Simplification rules
% 2.88/1.50  ----------------------
% 2.88/1.50  #Subsume      : 45
% 2.88/1.50  #Demod        : 51
% 2.88/1.50  #Tautology    : 18
% 2.88/1.50  #SimpNegUnit  : 6
% 2.88/1.50  #BackRed      : 0
% 2.88/1.50  
% 2.88/1.50  #Partial instantiations: 0
% 2.88/1.50  #Strategies tried      : 1
% 2.88/1.50  
% 2.88/1.50  Timing (in seconds)
% 2.88/1.50  ----------------------
% 2.88/1.50  Preprocessing        : 0.33
% 2.88/1.50  Parsing              : 0.17
% 2.88/1.50  CNF conversion       : 0.03
% 2.88/1.50  Main loop            : 0.34
% 2.88/1.50  Inferencing          : 0.13
% 2.88/1.50  Reduction            : 0.09
% 2.88/1.50  Demodulation         : 0.06
% 2.88/1.50  BG Simplification    : 0.02
% 2.88/1.50  Subsumption          : 0.08
% 2.88/1.50  Abstraction          : 0.01
% 2.88/1.50  MUC search           : 0.00
% 2.88/1.50  Cooper               : 0.00
% 2.88/1.50  Total                : 0.70
% 2.88/1.50  Index Insertion      : 0.00
% 2.88/1.50  Index Deletion       : 0.00
% 2.88/1.50  Index Matching       : 0.00
% 2.88/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
