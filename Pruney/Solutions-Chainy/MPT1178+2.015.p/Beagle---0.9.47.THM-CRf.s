%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 138 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 369 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_127,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
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

tff(f_109,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_172,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(k4_orders_2(A_67,B_68))
      | ~ m1_orders_1(B_68,k1_orders_1(u1_struct_0(A_67)))
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_178,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_175])).

tff(c_179,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_178])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [B_64,A_65] :
      ( k3_tarski(B_64) = A_65
      | ~ r1_tarski(k3_tarski(B_64),A_65)
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_155,plain,(
    ! [A_65] :
      ( k3_tarski(k4_orders_2('#skF_4','#skF_5')) = A_65
      | ~ r1_tarski(k1_xboole_0,A_65)
      | ~ r2_hidden(A_65,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_148])).

tff(c_165,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ r2_hidden(A_66,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40,c_155])).

tff(c_170,plain,
    ( '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_171,plain,(
    v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_171])).

tff(c_182,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_181,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_198,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_4])).

tff(c_201,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_198])).

tff(c_258,plain,(
    ! [D_79,A_80,B_81] :
      ( m2_orders_2(D_79,A_80,B_81)
      | ~ r2_hidden(D_79,k4_orders_2(A_80,B_81))
      | ~ m1_orders_1(B_81,k1_orders_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_262,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_258])).

tff(c_272,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_262])).

tff(c_273,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_272])).

tff(c_285,plain,(
    ! [B_82,A_83,C_84] :
      ( r2_hidden(k1_funct_1(B_82,u1_struct_0(A_83)),C_84)
      | ~ m2_orders_2(C_84,A_83,B_82)
      | ~ m1_orders_1(B_82,k1_orders_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_52,B_53] : ~ r2_hidden(A_52,k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_83])).

tff(c_314,plain,(
    ! [A_85,B_86] :
      ( ~ m2_orders_2(k1_xboole_0,A_85,B_86)
      | ~ m1_orders_1(B_86,k1_orders_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_285,c_89])).

tff(c_317,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_314])).

tff(c_320,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_273,c_317])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.21/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.21/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.27  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.21/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.27  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.21/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.21/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.21/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.21/1.27  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.27  
% 2.21/1.28  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.21/1.28  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.21/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.21/1.28  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.21/1.28  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.21/1.28  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.28  tff(f_74, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.21/1.28  tff(f_109, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.21/1.28  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.21/1.28  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.21/1.28  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_42, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_172, plain, (![A_67, B_68]: (~v1_xboole_0(k4_orders_2(A_67, B_68)) | ~m1_orders_1(B_68, k1_orders_1(u1_struct_0(A_67))) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.21/1.28  tff(c_175, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_172])).
% 2.21/1.28  tff(c_178, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_175])).
% 2.21/1.28  tff(c_179, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_178])).
% 2.21/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.28  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.28  tff(c_40, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.21/1.28  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.28  tff(c_105, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.28  tff(c_148, plain, (![B_64, A_65]: (k3_tarski(B_64)=A_65 | ~r1_tarski(k3_tarski(B_64), A_65) | ~r2_hidden(A_65, B_64))), inference(resolution, [status(thm)], [c_14, c_105])).
% 2.21/1.28  tff(c_155, plain, (![A_65]: (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=A_65 | ~r1_tarski(k1_xboole_0, A_65) | ~r2_hidden(A_65, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_148])).
% 2.21/1.28  tff(c_165, plain, (![A_66]: (k1_xboole_0=A_66 | ~r2_hidden(A_66, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40, c_155])).
% 2.21/1.28  tff(c_170, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_165])).
% 2.21/1.28  tff(c_171, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_170])).
% 2.21/1.28  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_171])).
% 2.21/1.28  tff(c_182, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_170])).
% 2.21/1.28  tff(c_181, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_170])).
% 2.21/1.28  tff(c_198, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_4])).
% 2.21/1.28  tff(c_201, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_182, c_198])).
% 2.21/1.28  tff(c_258, plain, (![D_79, A_80, B_81]: (m2_orders_2(D_79, A_80, B_81) | ~r2_hidden(D_79, k4_orders_2(A_80, B_81)) | ~m1_orders_1(B_81, k1_orders_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.28  tff(c_262, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_201, c_258])).
% 2.21/1.28  tff(c_272, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_262])).
% 2.21/1.28  tff(c_273, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_272])).
% 2.21/1.28  tff(c_285, plain, (![B_82, A_83, C_84]: (r2_hidden(k1_funct_1(B_82, u1_struct_0(A_83)), C_84) | ~m2_orders_2(C_84, A_83, B_82) | ~m1_orders_1(B_82, k1_orders_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.21/1.28  tff(c_18, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.28  tff(c_83, plain, (![A_52, B_53]: (~r2_hidden(A_52, k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.28  tff(c_89, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_83])).
% 2.21/1.28  tff(c_314, plain, (![A_85, B_86]: (~m2_orders_2(k1_xboole_0, A_85, B_86) | ~m1_orders_1(B_86, k1_orders_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(resolution, [status(thm)], [c_285, c_89])).
% 2.21/1.28  tff(c_317, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_314])).
% 2.21/1.28  tff(c_320, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_273, c_317])).
% 2.21/1.28  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_320])).
% 2.21/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  Inference rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Ref     : 0
% 2.21/1.28  #Sup     : 53
% 2.21/1.28  #Fact    : 0
% 2.21/1.28  #Define  : 0
% 2.21/1.28  #Split   : 1
% 2.21/1.28  #Chain   : 0
% 2.21/1.28  #Close   : 0
% 2.21/1.28  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 6
% 2.21/1.28  #Demod        : 41
% 2.21/1.28  #Tautology    : 26
% 2.21/1.28  #SimpNegUnit  : 9
% 2.21/1.28  #BackRed      : 1
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.28  Preprocessing        : 0.31
% 2.21/1.28  Parsing              : 0.17
% 2.21/1.28  CNF conversion       : 0.03
% 2.21/1.28  Main loop            : 0.21
% 2.21/1.28  Inferencing          : 0.08
% 2.21/1.28  Reduction            : 0.06
% 2.21/1.29  Demodulation         : 0.04
% 2.21/1.29  BG Simplification    : 0.02
% 2.21/1.29  Subsumption          : 0.04
% 2.21/1.29  Abstraction          : 0.01
% 2.21/1.29  MUC search           : 0.00
% 2.21/1.29  Cooper               : 0.00
% 2.21/1.29  Total                : 0.56
% 2.21/1.29  Index Insertion      : 0.00
% 2.21/1.29  Index Deletion       : 0.00
% 2.21/1.29  Index Matching       : 0.00
% 2.21/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
