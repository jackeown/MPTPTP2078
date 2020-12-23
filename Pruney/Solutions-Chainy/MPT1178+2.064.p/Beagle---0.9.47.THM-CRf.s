%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:10 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 188 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_orders_2 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_108,negated_conjecture,(
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
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => m2_orders_2(k1_tarski(k1_funct_1(B,u1_struct_0(A))),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_orders_2)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ! [B_51,A_49] :
      ( m2_orders_2(k1_tarski(k1_funct_1(B_51,u1_struct_0(A_49))),A_49,B_51)
      | ~ m1_orders_1(B_51,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_282,plain,(
    ! [D_128,A_129,B_130] :
      ( r2_hidden(D_128,k4_orders_2(A_129,B_130))
      | ~ m2_orders_2(D_128,A_129,B_130)
      | ~ m1_orders_1(B_130,k1_orders_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    ! [D_128] :
      ( r2_hidden(D_128,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_128,'#skF_3','#skF_4')
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_282])).

tff(c_287,plain,(
    ! [D_128] :
      ( r2_hidden(D_128,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_128,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_284])).

tff(c_289,plain,(
    ! [D_131] :
      ( r2_hidden(D_131,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_131,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_287])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k1_tarski(A_20),B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_22] : k3_tarski(k1_tarski(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k3_tarski(A_62),k3_tarski(B_63))
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,k3_tarski(B_71))
      | ~ r1_tarski(k1_tarski(A_70),B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_81])).

tff(c_118,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k3_tarski(B_73))
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_129,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,k1_xboole_0)
      | ~ r2_hidden(A_72,k4_orders_2('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_118])).

tff(c_344,plain,(
    ! [D_132] :
      ( r1_tarski(D_132,k1_xboole_0)
      | ~ m2_orders_2(D_132,'#skF_3','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_289,c_129])).

tff(c_348,plain,
    ( r1_tarski(k1_tarski(k1_funct_1('#skF_4',u1_struct_0('#skF_3'))),k1_xboole_0)
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_344])).

tff(c_351,plain,
    ( r1_tarski(k1_tarski(k1_funct_1('#skF_4',u1_struct_0('#skF_3'))),k1_xboole_0)
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_348])).

tff(c_352,plain,(
    r1_tarski(k1_tarski(k1_funct_1('#skF_4',u1_struct_0('#skF_3'))),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_351])).

tff(c_14,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | ~ r1_tarski(k1_tarski(A_20),B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_360,plain,(
    r2_hidden(k1_funct_1('#skF_4',u1_struct_0('#skF_3')),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_352,c_14])).

tff(c_22,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_368,plain,(
    ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_360,c_22])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.82  
% 3.16/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.82  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_orders_2 > k2_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.16/1.82  
% 3.16/1.82  %Foreground sorts:
% 3.16/1.82  
% 3.16/1.82  
% 3.16/1.82  %Background operators:
% 3.16/1.82  
% 3.16/1.82  
% 3.16/1.82  %Foreground operators:
% 3.16/1.82  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 3.16/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.16/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.82  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.16/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.82  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.16/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.82  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.16/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.82  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.82  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.16/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.82  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.16/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.82  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.16/1.82  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.16/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.82  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.82  
% 3.39/1.84  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.39/1.84  tff(f_108, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 3.39/1.84  tff(f_90, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => m2_orders_2(k1_tarski(k1_funct_1(B, u1_struct_0(A))), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_orders_2)).
% 3.39/1.84  tff(f_74, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 3.39/1.84  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.39/1.84  tff(f_43, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.39/1.84  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 3.39/1.84  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.39/1.84  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.84  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_48, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_46, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_44, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_42, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_40, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_36, plain, (![B_51, A_49]: (m2_orders_2(k1_tarski(k1_funct_1(B_51, u1_struct_0(A_49))), A_49, B_51) | ~m1_orders_1(B_51, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.84  tff(c_282, plain, (![D_128, A_129, B_130]: (r2_hidden(D_128, k4_orders_2(A_129, B_130)) | ~m2_orders_2(D_128, A_129, B_130) | ~m1_orders_1(B_130, k1_orders_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.84  tff(c_284, plain, (![D_128]: (r2_hidden(D_128, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_128, '#skF_3', '#skF_4') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_282])).
% 3.39/1.84  tff(c_287, plain, (![D_128]: (r2_hidden(D_128, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_128, '#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_284])).
% 3.39/1.84  tff(c_289, plain, (![D_131]: (r2_hidden(D_131, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_131, '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_287])).
% 3.39/1.84  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_3', '#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.84  tff(c_16, plain, (![A_20, B_21]: (r1_tarski(k1_tarski(A_20), B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.84  tff(c_18, plain, (![A_22]: (k3_tarski(k1_tarski(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.84  tff(c_81, plain, (![A_62, B_63]: (r1_tarski(k3_tarski(A_62), k3_tarski(B_63)) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.84  tff(c_113, plain, (![A_70, B_71]: (r1_tarski(A_70, k3_tarski(B_71)) | ~r1_tarski(k1_tarski(A_70), B_71))), inference(superposition, [status(thm), theory('equality')], [c_18, c_81])).
% 3.39/1.84  tff(c_118, plain, (![A_72, B_73]: (r1_tarski(A_72, k3_tarski(B_73)) | ~r2_hidden(A_72, B_73))), inference(resolution, [status(thm)], [c_16, c_113])).
% 3.39/1.84  tff(c_129, plain, (![A_72]: (r1_tarski(A_72, k1_xboole_0) | ~r2_hidden(A_72, k4_orders_2('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_118])).
% 3.39/1.84  tff(c_344, plain, (![D_132]: (r1_tarski(D_132, k1_xboole_0) | ~m2_orders_2(D_132, '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_289, c_129])).
% 3.39/1.84  tff(c_348, plain, (r1_tarski(k1_tarski(k1_funct_1('#skF_4', u1_struct_0('#skF_3'))), k1_xboole_0) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_344])).
% 3.39/1.84  tff(c_351, plain, (r1_tarski(k1_tarski(k1_funct_1('#skF_4', u1_struct_0('#skF_3'))), k1_xboole_0) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_348])).
% 3.39/1.84  tff(c_352, plain, (r1_tarski(k1_tarski(k1_funct_1('#skF_4', u1_struct_0('#skF_3'))), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_351])).
% 3.39/1.84  tff(c_14, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | ~r1_tarski(k1_tarski(A_20), B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.84  tff(c_360, plain, (r2_hidden(k1_funct_1('#skF_4', u1_struct_0('#skF_3')), k1_xboole_0)), inference(resolution, [status(thm)], [c_352, c_14])).
% 3.39/1.84  tff(c_22, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.84  tff(c_368, plain, (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_4', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_360, c_22])).
% 3.39/1.84  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_368])).
% 3.39/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.84  
% 3.39/1.84  Inference rules
% 3.39/1.84  ----------------------
% 3.39/1.84  #Ref     : 0
% 3.39/1.84  #Sup     : 67
% 3.39/1.84  #Fact    : 0
% 3.39/1.84  #Define  : 0
% 3.39/1.84  #Split   : 0
% 3.39/1.84  #Chain   : 0
% 3.39/1.84  #Close   : 0
% 3.39/1.84  
% 3.39/1.84  Ordering : KBO
% 3.39/1.84  
% 3.39/1.84  Simplification rules
% 3.39/1.84  ----------------------
% 3.39/1.84  #Subsume      : 2
% 3.39/1.84  #Demod        : 18
% 3.39/1.84  #Tautology    : 18
% 3.39/1.84  #SimpNegUnit  : 2
% 3.39/1.84  #BackRed      : 0
% 3.39/1.84  
% 3.39/1.84  #Partial instantiations: 0
% 3.39/1.84  #Strategies tried      : 1
% 3.39/1.84  
% 3.39/1.84  Timing (in seconds)
% 3.39/1.84  ----------------------
% 3.39/1.85  Preprocessing        : 0.54
% 3.39/1.85  Parsing              : 0.28
% 3.39/1.85  CNF conversion       : 0.04
% 3.39/1.85  Main loop            : 0.45
% 3.39/1.85  Inferencing          : 0.16
% 3.39/1.85  Reduction            : 0.13
% 3.39/1.85  Demodulation         : 0.10
% 3.39/1.85  BG Simplification    : 0.03
% 3.39/1.85  Subsumption          : 0.10
% 3.39/1.85  Abstraction          : 0.02
% 3.39/1.85  MUC search           : 0.00
% 3.39/1.85  Cooper               : 0.00
% 3.39/1.85  Total                : 1.04
% 3.39/1.85  Index Insertion      : 0.00
% 3.39/1.85  Index Deletion       : 0.00
% 3.39/1.85  Index Matching       : 0.00
% 3.39/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
