%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 141 expanded)
%              Number of leaves         :   52 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 315 expanded)
%              Number of equality atoms :   18 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_subset_1 > k4_orders_2 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_174,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_119,axiom,(
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

tff(f_156,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(A))))))
        & ~ r1_xboole_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e5_6__mcart_1)).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    ! [C_79,A_80] :
      ( r2_hidden(C_79,k1_zfmisc_1(A_80))
      | ~ r1_tarski(C_79,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [C_79] :
      ( r2_hidden(C_79,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(C_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_150])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_90,plain,(
    v3_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_88,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_86,plain,(
    v5_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_84,plain,(
    l1_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_82,plain,(
    m1_orders_1('#skF_10',k1_orders_1(u1_struct_0('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    k3_tarski(k4_orders_2('#skF_9','#skF_10')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_125,plain,(
    ! [A_72] : r1_tarski(A_72,k1_zfmisc_1(k3_tarski(A_72))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_128,plain,(
    r1_tarski(k4_orders_2('#skF_9','#skF_10'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_125])).

tff(c_129,plain,(
    r1_tarski(k4_orders_2('#skF_9','#skF_10'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_128])).

tff(c_186,plain,(
    ! [B_89,A_90] :
      ( k1_tarski(B_89) = A_90
      | k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_tarski(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_197,plain,
    ( k4_orders_2('#skF_9','#skF_10') = k1_tarski(k1_xboole_0)
    | k4_orders_2('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_186])).

tff(c_308,plain,(
    k4_orders_2('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_754,plain,(
    ! [A_127,B_128] :
      ( ~ v1_xboole_0(k4_orders_2(A_127,B_128))
      | ~ m1_orders_1(B_128,k1_orders_1(u1_struct_0(A_127)))
      | ~ l1_orders_2(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_757,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_9','#skF_10'))
    | ~ l1_orders_2('#skF_9')
    | ~ v5_orders_2('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | ~ v3_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_754])).

tff(c_760,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_2,c_308,c_757])).

tff(c_762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_760])).

tff(c_763,plain,(
    k4_orders_2('#skF_9','#skF_10') = k1_tarski(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_1327,plain,(
    ! [D_161,A_162,B_163] :
      ( m2_orders_2(D_161,A_162,B_163)
      | ~ r2_hidden(D_161,k4_orders_2(A_162,B_163))
      | ~ m1_orders_1(B_163,k1_orders_1(u1_struct_0(A_162)))
      | ~ l1_orders_2(A_162)
      | ~ v5_orders_2(A_162)
      | ~ v4_orders_2(A_162)
      | ~ v3_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1350,plain,(
    ! [D_161] :
      ( m2_orders_2(D_161,'#skF_9','#skF_10')
      | ~ r2_hidden(D_161,k1_tarski(k1_xboole_0))
      | ~ m1_orders_1('#skF_10',k1_orders_1(u1_struct_0('#skF_9')))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1327])).

tff(c_1368,plain,(
    ! [D_161] :
      ( m2_orders_2(D_161,'#skF_9','#skF_10')
      | ~ r2_hidden(D_161,k1_tarski(k1_xboole_0))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_1350])).

tff(c_1373,plain,(
    ! [D_164] :
      ( m2_orders_2(D_164,'#skF_9','#skF_10')
      | ~ r2_hidden(D_164,k1_tarski(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1368])).

tff(c_1431,plain,(
    ! [C_79] :
      ( m2_orders_2(C_79,'#skF_9','#skF_10')
      | ~ r1_tarski(C_79,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_153,c_1373])).

tff(c_1611,plain,(
    ! [B_182,A_183,C_184] :
      ( r2_hidden(k1_funct_1(B_182,u1_struct_0(A_183)),C_184)
      | ~ m2_orders_2(C_184,A_183,B_182)
      | ~ m1_orders_1(B_182,k1_orders_1(u1_struct_0(A_183)))
      | ~ l1_orders_2(A_183)
      | ~ v5_orders_2(A_183)
      | ~ v4_orders_2(A_183)
      | ~ v3_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_10,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_132,plain,(
    ! [C_75,A_76] :
      ( ~ r1_xboole_0(C_75,A_76)
      | ~ r2_hidden(C_75,'#skF_4'(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_214,plain,(
    ! [A_92] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4'(A_92)),A_92)
      | '#skF_4'(A_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_132])).

tff(c_219,plain,(
    '#skF_4'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_214])).

tff(c_42,plain,(
    ! [C_24,A_19] :
      ( ~ r1_xboole_0(C_24,A_19)
      | ~ r2_hidden(C_24,'#skF_4'(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_226,plain,(
    ! [C_24] :
      ( ~ r1_xboole_0(C_24,k1_xboole_0)
      | ~ r2_hidden(C_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_42])).

tff(c_232,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_3343,plain,(
    ! [A_274,B_275] :
      ( ~ m2_orders_2(k1_xboole_0,A_274,B_275)
      | ~ m1_orders_1(B_275,k1_orders_1(u1_struct_0(A_274)))
      | ~ l1_orders_2(A_274)
      | ~ v5_orders_2(A_274)
      | ~ v4_orders_2(A_274)
      | ~ v3_orders_2(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_1611,c_232])).

tff(c_3346,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_9','#skF_10')
    | ~ l1_orders_2('#skF_9')
    | ~ v5_orders_2('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | ~ v3_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_3343])).

tff(c_3349,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_9','#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_3346])).

tff(c_3350,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3349])).

tff(c_3353,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1431,c_3350])).

tff(c_3357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.97  
% 5.15/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.97  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_subset_1 > k4_orders_2 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_6
% 5.15/1.97  
% 5.15/1.97  %Foreground sorts:
% 5.15/1.97  
% 5.15/1.97  
% 5.15/1.97  %Background operators:
% 5.15/1.97  
% 5.15/1.97  
% 5.15/1.97  %Foreground operators:
% 5.15/1.97  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 5.15/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.15/1.97  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.15/1.97  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.15/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.97  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.15/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.15/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/1.97  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.15/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.15/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.97  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.15/1.97  tff('#skF_10', type, '#skF_10': $i).
% 5.15/1.97  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.15/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.15/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.15/1.97  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.15/1.97  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.15/1.97  tff('#skF_9', type, '#skF_9': $i).
% 5.15/1.97  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.15/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.97  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.15/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.15/1.97  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.15/1.97  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.15/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.15/1.97  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.15/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.15/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.15/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.15/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/1.97  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.15/1.97  
% 5.15/1.99  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.15/1.99  tff(f_62, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 5.15/1.99  tff(f_51, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.15/1.99  tff(f_174, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 5.15/1.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.15/1.99  tff(f_61, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 5.15/1.99  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.15/1.99  tff(f_137, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 5.15/1.99  tff(f_119, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 5.15/1.99  tff(f_156, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 5.15/1.99  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.15/1.99  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.15/1.99  tff(f_74, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(A)))))) & ~r1_xboole_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e5_6__mcart_1)).
% 5.15/1.99  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.15/1.99  tff(c_36, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.15/1.99  tff(c_150, plain, (![C_79, A_80]: (r2_hidden(C_79, k1_zfmisc_1(A_80)) | ~r1_tarski(C_79, A_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.15/1.99  tff(c_153, plain, (![C_79]: (r2_hidden(C_79, k1_tarski(k1_xboole_0)) | ~r1_tarski(C_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_150])).
% 5.15/1.99  tff(c_92, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_90, plain, (v3_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_88, plain, (v4_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_86, plain, (v5_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_84, plain, (l1_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_82, plain, (m1_orders_1('#skF_10', k1_orders_1(u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.15/1.99  tff(c_80, plain, (k3_tarski(k4_orders_2('#skF_9', '#skF_10'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.15/1.99  tff(c_125, plain, (![A_72]: (r1_tarski(A_72, k1_zfmisc_1(k3_tarski(A_72))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.15/1.99  tff(c_128, plain, (r1_tarski(k4_orders_2('#skF_9', '#skF_10'), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_80, c_125])).
% 5.15/1.99  tff(c_129, plain, (r1_tarski(k4_orders_2('#skF_9', '#skF_10'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_128])).
% 5.15/1.99  tff(c_186, plain, (![B_89, A_90]: (k1_tarski(B_89)=A_90 | k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_tarski(B_89)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.15/1.99  tff(c_197, plain, (k4_orders_2('#skF_9', '#skF_10')=k1_tarski(k1_xboole_0) | k4_orders_2('#skF_9', '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_186])).
% 5.15/1.99  tff(c_308, plain, (k4_orders_2('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_197])).
% 5.15/1.99  tff(c_754, plain, (![A_127, B_128]: (~v1_xboole_0(k4_orders_2(A_127, B_128)) | ~m1_orders_1(B_128, k1_orders_1(u1_struct_0(A_127))) | ~l1_orders_2(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/1.99  tff(c_757, plain, (~v1_xboole_0(k4_orders_2('#skF_9', '#skF_10')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_82, c_754])).
% 5.15/1.99  tff(c_760, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_2, c_308, c_757])).
% 5.15/1.99  tff(c_762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_760])).
% 5.15/1.99  tff(c_763, plain, (k4_orders_2('#skF_9', '#skF_10')=k1_tarski(k1_xboole_0)), inference(splitRight, [status(thm)], [c_197])).
% 5.15/1.99  tff(c_1327, plain, (![D_161, A_162, B_163]: (m2_orders_2(D_161, A_162, B_163) | ~r2_hidden(D_161, k4_orders_2(A_162, B_163)) | ~m1_orders_1(B_163, k1_orders_1(u1_struct_0(A_162))) | ~l1_orders_2(A_162) | ~v5_orders_2(A_162) | ~v4_orders_2(A_162) | ~v3_orders_2(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.15/1.99  tff(c_1350, plain, (![D_161]: (m2_orders_2(D_161, '#skF_9', '#skF_10') | ~r2_hidden(D_161, k1_tarski(k1_xboole_0)) | ~m1_orders_1('#skF_10', k1_orders_1(u1_struct_0('#skF_9'))) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_763, c_1327])).
% 5.15/1.99  tff(c_1368, plain, (![D_161]: (m2_orders_2(D_161, '#skF_9', '#skF_10') | ~r2_hidden(D_161, k1_tarski(k1_xboole_0)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_1350])).
% 5.15/1.99  tff(c_1373, plain, (![D_164]: (m2_orders_2(D_164, '#skF_9', '#skF_10') | ~r2_hidden(D_164, k1_tarski(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_92, c_1368])).
% 5.15/1.99  tff(c_1431, plain, (![C_79]: (m2_orders_2(C_79, '#skF_9', '#skF_10') | ~r1_tarski(C_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_153, c_1373])).
% 5.15/1.99  tff(c_1611, plain, (![B_182, A_183, C_184]: (r2_hidden(k1_funct_1(B_182, u1_struct_0(A_183)), C_184) | ~m2_orders_2(C_184, A_183, B_182) | ~m1_orders_1(B_182, k1_orders_1(u1_struct_0(A_183))) | ~l1_orders_2(A_183) | ~v5_orders_2(A_183) | ~v4_orders_2(A_183) | ~v3_orders_2(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.15/1.99  tff(c_10, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.15/1.99  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.15/1.99  tff(c_132, plain, (![C_75, A_76]: (~r1_xboole_0(C_75, A_76) | ~r2_hidden(C_75, '#skF_4'(A_76)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.15/1.99  tff(c_214, plain, (![A_92]: (~r1_xboole_0('#skF_1'('#skF_4'(A_92)), A_92) | '#skF_4'(A_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_132])).
% 5.15/1.99  tff(c_219, plain, ('#skF_4'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_214])).
% 5.15/1.99  tff(c_42, plain, (![C_24, A_19]: (~r1_xboole_0(C_24, A_19) | ~r2_hidden(C_24, '#skF_4'(A_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.15/1.99  tff(c_226, plain, (![C_24]: (~r1_xboole_0(C_24, k1_xboole_0) | ~r2_hidden(C_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_219, c_42])).
% 5.15/1.99  tff(c_232, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_226])).
% 5.15/1.99  tff(c_3343, plain, (![A_274, B_275]: (~m2_orders_2(k1_xboole_0, A_274, B_275) | ~m1_orders_1(B_275, k1_orders_1(u1_struct_0(A_274))) | ~l1_orders_2(A_274) | ~v5_orders_2(A_274) | ~v4_orders_2(A_274) | ~v3_orders_2(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_1611, c_232])).
% 5.15/1.99  tff(c_3346, plain, (~m2_orders_2(k1_xboole_0, '#skF_9', '#skF_10') | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_82, c_3343])).
% 5.15/1.99  tff(c_3349, plain, (~m2_orders_2(k1_xboole_0, '#skF_9', '#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_3346])).
% 5.15/1.99  tff(c_3350, plain, (~m2_orders_2(k1_xboole_0, '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_92, c_3349])).
% 5.15/1.99  tff(c_3353, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1431, c_3350])).
% 5.15/1.99  tff(c_3357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3353])).
% 5.15/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.99  
% 5.15/1.99  Inference rules
% 5.15/1.99  ----------------------
% 5.15/1.99  #Ref     : 0
% 5.15/1.99  #Sup     : 667
% 5.15/1.99  #Fact    : 2
% 5.15/1.99  #Define  : 0
% 5.15/1.99  #Split   : 13
% 5.15/1.99  #Chain   : 0
% 5.15/1.99  #Close   : 0
% 5.15/1.99  
% 5.15/1.99  Ordering : KBO
% 5.15/1.99  
% 5.15/1.99  Simplification rules
% 5.15/1.99  ----------------------
% 5.15/1.99  #Subsume      : 116
% 5.15/1.99  #Demod        : 512
% 5.15/1.99  #Tautology    : 193
% 5.15/1.99  #SimpNegUnit  : 83
% 5.15/1.99  #BackRed      : 12
% 5.15/1.99  
% 5.15/1.99  #Partial instantiations: 0
% 5.15/1.99  #Strategies tried      : 1
% 5.15/1.99  
% 5.15/1.99  Timing (in seconds)
% 5.15/1.99  ----------------------
% 5.15/1.99  Preprocessing        : 0.36
% 5.15/1.99  Parsing              : 0.18
% 5.15/1.99  CNF conversion       : 0.03
% 5.15/1.99  Main loop            : 0.86
% 5.15/1.99  Inferencing          : 0.29
% 5.15/1.99  Reduction            : 0.29
% 5.15/1.99  Demodulation         : 0.20
% 5.15/1.99  BG Simplification    : 0.04
% 5.15/1.99  Subsumption          : 0.17
% 5.15/1.99  Abstraction          : 0.05
% 5.15/1.99  MUC search           : 0.00
% 5.15/1.99  Cooper               : 0.00
% 5.15/1.99  Total                : 1.25
% 5.15/1.99  Index Insertion      : 0.00
% 5.15/1.99  Index Deletion       : 0.00
% 5.15/1.99  Index Matching       : 0.00
% 5.15/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
