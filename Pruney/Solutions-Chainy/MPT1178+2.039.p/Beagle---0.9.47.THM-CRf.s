%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:07 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 110 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 332 expanded)
%              Number of equality atoms :    3 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_120,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_67,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_102,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_102,plain,(
    ! [A_59,B_60] :
      ( m2_orders_2('#skF_4'(A_59,B_60),A_59,B_60)
      | ~ m1_orders_1(B_60,k1_orders_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_104,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_102])).

tff(c_107,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_104])).

tff(c_108,plain,(
    m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_107])).

tff(c_114,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,k4_orders_2(A_65,B_66))
      | ~ m2_orders_2(D_64,A_65,B_66)
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_65)))
      | ~ l1_orders_2(A_65)
      | ~ v5_orders_2(A_65)
      | ~ v4_orders_2(A_65)
      | ~ v3_orders_2(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_64,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_114])).

tff(c_119,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_64,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_116])).

tff(c_121,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_67,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_119])).

tff(c_28,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k3_tarski(B_48))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k1_xboole_0)
      | ~ r2_hidden(A_47,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_52])).

tff(c_136,plain,(
    ! [D_68] :
      ( r1_tarski(D_68,k1_xboole_0)
      | ~ m2_orders_2(D_68,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_121,c_55])).

tff(c_140,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_108,c_136])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [B_49,A_50] :
      ( ~ r1_xboole_0(B_49,A_50)
      | ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_144,plain,(
    v1_xboole_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_140,c_60])).

tff(c_145,plain,(
    ! [B_69,A_70,C_71] :
      ( r2_hidden(k1_funct_1(B_69,u1_struct_0(A_70)),C_71)
      | ~ m2_orders_2(C_71,A_70,B_69)
      | ~ m1_orders_1(B_69,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [C_72,A_73,B_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m2_orders_2(C_72,A_73,B_74)
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_161,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_159])).

tff(c_164,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_144,c_161])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.09/1.24  
% 2.09/1.24  %Foreground sorts:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Background operators:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Foreground operators:
% 2.09/1.24  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.09/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.09/1.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.24  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.09/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.24  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.09/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.09/1.24  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.09/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.09/1.24  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.09/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.09/1.24  
% 2.20/1.26  tff(f_120, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.20/1.26  tff(f_83, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.20/1.26  tff(f_67, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.20/1.26  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.20/1.26  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.20/1.26  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.20/1.26  tff(f_102, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.20/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.26  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_38, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_36, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_34, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_32, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_30, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_102, plain, (![A_59, B_60]: (m2_orders_2('#skF_4'(A_59, B_60), A_59, B_60) | ~m1_orders_1(B_60, k1_orders_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.26  tff(c_104, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_102])).
% 2.20/1.26  tff(c_107, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_104])).
% 2.20/1.26  tff(c_108, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_107])).
% 2.20/1.26  tff(c_114, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, k4_orders_2(A_65, B_66)) | ~m2_orders_2(D_64, A_65, B_66) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_65))) | ~l1_orders_2(A_65) | ~v5_orders_2(A_65) | ~v4_orders_2(A_65) | ~v3_orders_2(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.20/1.26  tff(c_116, plain, (![D_64]: (r2_hidden(D_64, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_64, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_114])).
% 2.20/1.26  tff(c_119, plain, (![D_64]: (r2_hidden(D_64, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_64, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_116])).
% 2.20/1.26  tff(c_121, plain, (![D_67]: (r2_hidden(D_67, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_67, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_40, c_119])).
% 2.20/1.26  tff(c_28, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.20/1.26  tff(c_52, plain, (![A_47, B_48]: (r1_tarski(A_47, k3_tarski(B_48)) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.20/1.26  tff(c_55, plain, (![A_47]: (r1_tarski(A_47, k1_xboole_0) | ~r2_hidden(A_47, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_52])).
% 2.20/1.26  tff(c_136, plain, (![D_68]: (r1_tarski(D_68, k1_xboole_0) | ~m2_orders_2(D_68, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_121, c_55])).
% 2.20/1.26  tff(c_140, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), k1_xboole_0)), inference(resolution, [status(thm)], [c_108, c_136])).
% 2.20/1.26  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.26  tff(c_56, plain, (![B_49, A_50]: (~r1_xboole_0(B_49, A_50) | ~r1_tarski(B_49, A_50) | v1_xboole_0(B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.26  tff(c_60, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.20/1.26  tff(c_144, plain, (v1_xboole_0('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_140, c_60])).
% 2.20/1.26  tff(c_145, plain, (![B_69, A_70, C_71]: (r2_hidden(k1_funct_1(B_69, u1_struct_0(A_70)), C_71) | ~m2_orders_2(C_71, A_70, B_69) | ~m1_orders_1(B_69, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.20/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.26  tff(c_159, plain, (![C_72, A_73, B_74]: (~v1_xboole_0(C_72) | ~m2_orders_2(C_72, A_73, B_74) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_145, c_2])).
% 2.20/1.26  tff(c_161, plain, (~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_108, c_159])).
% 2.20/1.26  tff(c_164, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_144, c_161])).
% 2.20/1.26  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_164])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 23
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 1
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 2
% 2.20/1.26  #Demod        : 28
% 2.20/1.26  #Tautology    : 4
% 2.20/1.26  #SimpNegUnit  : 7
% 2.20/1.26  #BackRed      : 1
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.26  Preprocessing        : 0.30
% 2.20/1.26  Parsing              : 0.16
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.17
% 2.20/1.26  Inferencing          : 0.07
% 2.20/1.26  Reduction            : 0.05
% 2.20/1.26  Demodulation         : 0.03
% 2.20/1.26  BG Simplification    : 0.01
% 2.20/1.26  Subsumption          : 0.02
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.50
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
