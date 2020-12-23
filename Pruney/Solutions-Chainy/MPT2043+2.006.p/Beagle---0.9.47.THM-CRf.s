%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:23 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   70 (  91 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 156 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k2_subset_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_58,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_64,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))
     => ( v13_waybel_0(B,k3_yellow_1(A))
      <=> ! [C,D] :
            ( ( r1_tarski(C,D)
              & r1_tarski(D,A)
              & r2_hidden(C,B) )
           => r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_14] : ~ v1_subset_1(k2_subset_1(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [A_14] : ~ v1_subset_1(A_14,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_48,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    ! [A_17] : k9_setfam_1(A_17) = k1_zfmisc_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_19] : k2_yellow_1(k9_setfam_1(A_19)) = k3_yellow_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [A_38] : k2_yellow_1(k1_zfmisc_1(A_38)) = k3_yellow_1(A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_26,plain,(
    ! [A_18] : u1_struct_0(k2_yellow_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [A_38] : u1_struct_0(k3_yellow_1(A_38)) = k1_zfmisc_1(A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_26])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_131,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_46])).

tff(c_42,plain,(
    v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_152,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_49,B_50] :
      ( ~ v1_xboole_0(A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_251,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_3'(A_68,B_69),A_68)
      | B_69 = A_68
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_256,plain,(
    ! [B_16,B_69] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(B_16),B_69),B_16)
      | k1_zfmisc_1(B_16) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(B_16))) ) ),
    inference(resolution,[status(thm)],[c_251,c_20])).

tff(c_44,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [D_27,B_21,C_26,A_20] :
      ( r2_hidden(D_27,B_21)
      | ~ r2_hidden(C_26,B_21)
      | ~ r1_tarski(D_27,A_20)
      | ~ r1_tarski(C_26,D_27)
      | ~ v13_waybel_0(B_21,k3_yellow_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20)))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2563,plain,(
    ! [D_292,B_293,C_294,A_295] :
      ( r2_hidden(D_292,B_293)
      | ~ r2_hidden(C_294,B_293)
      | ~ r1_tarski(D_292,A_295)
      | ~ r1_tarski(C_294,D_292)
      | ~ v13_waybel_0(B_293,k3_yellow_1(A_295))
      | ~ m1_subset_1(B_293,k1_zfmisc_1(k1_zfmisc_1(A_295))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_32])).

tff(c_2683,plain,(
    ! [D_303,A_304] :
      ( r2_hidden(D_303,'#skF_7')
      | ~ r1_tarski(D_303,A_304)
      | ~ r1_tarski('#skF_8',D_303)
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(A_304))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(A_304))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2563])).

tff(c_3468,plain,(
    ! [B_353,B_354] :
      ( r2_hidden('#skF_3'(k1_zfmisc_1(B_353),B_354),'#skF_7')
      | ~ r1_tarski('#skF_8','#skF_3'(k1_zfmisc_1(B_353),B_354))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(B_353))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(B_353)))
      | k1_zfmisc_1(B_353) = B_354
      | ~ m1_subset_1(B_354,k1_zfmisc_1(k1_zfmisc_1(B_353))) ) ),
    inference(resolution,[status(thm)],[c_256,c_2683])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_3'(A_11,B_12),B_12)
      | B_12 = A_11
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4519,plain,(
    ! [B_445] :
      ( ~ r1_tarski('#skF_8','#skF_3'(k1_zfmisc_1(B_445),'#skF_7'))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(B_445))
      | k1_zfmisc_1(B_445) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(B_445))) ) ),
    inference(resolution,[status(thm)],[c_3468,c_14])).

tff(c_4522,plain,(
    ! [B_445] :
      ( ~ v13_waybel_0('#skF_7',k3_yellow_1(B_445))
      | k1_zfmisc_1(B_445) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(B_445)))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_161,c_4519])).

tff(c_4534,plain,(
    ! [B_446] :
      ( ~ v13_waybel_0('#skF_7',k3_yellow_1(B_446))
      | k1_zfmisc_1(B_446) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(B_446))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4522])).

tff(c_4540,plain,
    ( ~ v13_waybel_0('#skF_7',k3_yellow_1('#skF_6'))
    | k1_zfmisc_1('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_131,c_4534])).

tff(c_4544,plain,(
    k1_zfmisc_1('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4540])).

tff(c_52,plain,(
    v1_subset_1('#skF_7',u1_struct_0(k3_yellow_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_116,plain,(
    v1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_52])).

tff(c_4593,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4544,c_116])).

tff(c_4602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.31  
% 6.59/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.31  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k2_subset_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 6.59/2.31  
% 6.59/2.31  %Foreground sorts:
% 6.59/2.31  
% 6.59/2.31  
% 6.59/2.31  %Background operators:
% 6.59/2.31  
% 6.59/2.31  
% 6.59/2.31  %Foreground operators:
% 6.59/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.59/2.31  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 6.59/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.59/2.31  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.59/2.31  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 6.59/2.31  tff('#skF_7', type, '#skF_7': $i).
% 6.59/2.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.59/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.59/2.31  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 6.59/2.31  tff('#skF_6', type, '#skF_6': $i).
% 6.59/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.59/2.31  tff('#skF_8', type, '#skF_8': $i).
% 6.59/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.31  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 6.59/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.59/2.31  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.59/2.31  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 6.59/2.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.59/2.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.59/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.59/2.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.59/2.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.59/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.59/2.31  
% 6.59/2.32  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.59/2.32  tff(f_52, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 6.59/2.32  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 6.59/2.32  tff(f_58, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 6.59/2.32  tff(f_64, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 6.59/2.32  tff(f_62, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 6.59/2.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.59/2.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.59/2.32  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 6.59/2.32  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.59/2.32  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) => (v13_waybel_0(B, k3_yellow_1(A)) <=> (![C, D]: (((r1_tarski(C, D) & r1_tarski(D, A)) & r2_hidden(C, B)) => r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 6.59/2.32  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.59/2.32  tff(c_18, plain, (![A_14]: (~v1_subset_1(k2_subset_1(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.59/2.32  tff(c_58, plain, (![A_14]: (~v1_subset_1(A_14, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 6.59/2.32  tff(c_48, plain, (v13_waybel_0('#skF_7', k3_yellow_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.32  tff(c_24, plain, (![A_17]: (k9_setfam_1(A_17)=k1_zfmisc_1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.32  tff(c_30, plain, (![A_19]: (k2_yellow_1(k9_setfam_1(A_19))=k3_yellow_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.59/2.32  tff(c_92, plain, (![A_38]: (k2_yellow_1(k1_zfmisc_1(A_38))=k3_yellow_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 6.59/2.32  tff(c_26, plain, (![A_18]: (u1_struct_0(k2_yellow_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.32  tff(c_98, plain, (![A_38]: (u1_struct_0(k3_yellow_1(A_38))=k1_zfmisc_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_92, c_26])).
% 6.59/2.32  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.32  tff(c_131, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_46])).
% 6.59/2.32  tff(c_42, plain, (v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.32  tff(c_152, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.59/2.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.59/2.32  tff(c_161, plain, (![A_49, B_50]: (~v1_xboole_0(A_49) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_152, c_2])).
% 6.59/2.32  tff(c_251, plain, (![A_68, B_69]: (m1_subset_1('#skF_3'(A_68, B_69), A_68) | B_69=A_68 | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.59/2.32  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.59/2.32  tff(c_256, plain, (![B_16, B_69]: (r1_tarski('#skF_3'(k1_zfmisc_1(B_16), B_69), B_16) | k1_zfmisc_1(B_16)=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(B_16))))), inference(resolution, [status(thm)], [c_251, c_20])).
% 6.59/2.32  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.32  tff(c_32, plain, (![D_27, B_21, C_26, A_20]: (r2_hidden(D_27, B_21) | ~r2_hidden(C_26, B_21) | ~r1_tarski(D_27, A_20) | ~r1_tarski(C_26, D_27) | ~v13_waybel_0(B_21, k3_yellow_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20)))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.59/2.32  tff(c_2563, plain, (![D_292, B_293, C_294, A_295]: (r2_hidden(D_292, B_293) | ~r2_hidden(C_294, B_293) | ~r1_tarski(D_292, A_295) | ~r1_tarski(C_294, D_292) | ~v13_waybel_0(B_293, k3_yellow_1(A_295)) | ~m1_subset_1(B_293, k1_zfmisc_1(k1_zfmisc_1(A_295))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_32])).
% 6.59/2.32  tff(c_2683, plain, (![D_303, A_304]: (r2_hidden(D_303, '#skF_7') | ~r1_tarski(D_303, A_304) | ~r1_tarski('#skF_8', D_303) | ~v13_waybel_0('#skF_7', k3_yellow_1(A_304)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(A_304))))), inference(resolution, [status(thm)], [c_44, c_2563])).
% 6.59/2.32  tff(c_3468, plain, (![B_353, B_354]: (r2_hidden('#skF_3'(k1_zfmisc_1(B_353), B_354), '#skF_7') | ~r1_tarski('#skF_8', '#skF_3'(k1_zfmisc_1(B_353), B_354)) | ~v13_waybel_0('#skF_7', k3_yellow_1(B_353)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(B_353))) | k1_zfmisc_1(B_353)=B_354 | ~m1_subset_1(B_354, k1_zfmisc_1(k1_zfmisc_1(B_353))))), inference(resolution, [status(thm)], [c_256, c_2683])).
% 6.59/2.32  tff(c_14, plain, (![A_11, B_12]: (~r2_hidden('#skF_3'(A_11, B_12), B_12) | B_12=A_11 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.59/2.32  tff(c_4519, plain, (![B_445]: (~r1_tarski('#skF_8', '#skF_3'(k1_zfmisc_1(B_445), '#skF_7')) | ~v13_waybel_0('#skF_7', k3_yellow_1(B_445)) | k1_zfmisc_1(B_445)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(B_445))))), inference(resolution, [status(thm)], [c_3468, c_14])).
% 6.59/2.32  tff(c_4522, plain, (![B_445]: (~v13_waybel_0('#skF_7', k3_yellow_1(B_445)) | k1_zfmisc_1(B_445)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(B_445))) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_161, c_4519])).
% 6.59/2.32  tff(c_4534, plain, (![B_446]: (~v13_waybel_0('#skF_7', k3_yellow_1(B_446)) | k1_zfmisc_1(B_446)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(B_446))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4522])).
% 6.59/2.32  tff(c_4540, plain, (~v13_waybel_0('#skF_7', k3_yellow_1('#skF_6')) | k1_zfmisc_1('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_131, c_4534])).
% 6.59/2.32  tff(c_4544, plain, (k1_zfmisc_1('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4540])).
% 6.59/2.32  tff(c_52, plain, (v1_subset_1('#skF_7', u1_struct_0(k3_yellow_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.59/2.32  tff(c_116, plain, (v1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_52])).
% 6.59/2.32  tff(c_4593, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4544, c_116])).
% 6.59/2.32  tff(c_4602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4593])).
% 6.59/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.32  
% 6.59/2.32  Inference rules
% 6.59/2.32  ----------------------
% 6.59/2.32  #Ref     : 0
% 6.59/2.32  #Sup     : 1139
% 6.59/2.32  #Fact    : 0
% 6.59/2.32  #Define  : 0
% 6.59/2.32  #Split   : 36
% 6.59/2.32  #Chain   : 0
% 6.59/2.32  #Close   : 0
% 6.59/2.32  
% 6.59/2.32  Ordering : KBO
% 6.59/2.32  
% 6.59/2.32  Simplification rules
% 6.59/2.32  ----------------------
% 6.59/2.32  #Subsume      : 450
% 6.59/2.32  #Demod        : 246
% 6.59/2.32  #Tautology    : 86
% 6.59/2.32  #SimpNegUnit  : 10
% 6.59/2.32  #BackRed      : 75
% 6.59/2.32  
% 6.59/2.32  #Partial instantiations: 0
% 6.59/2.32  #Strategies tried      : 1
% 6.59/2.32  
% 6.59/2.32  Timing (in seconds)
% 6.59/2.32  ----------------------
% 6.59/2.33  Preprocessing        : 0.30
% 6.59/2.33  Parsing              : 0.16
% 6.59/2.33  CNF conversion       : 0.02
% 6.59/2.33  Main loop            : 1.25
% 6.59/2.33  Inferencing          : 0.38
% 6.59/2.33  Reduction            : 0.34
% 6.59/2.33  Demodulation         : 0.22
% 6.59/2.33  BG Simplification    : 0.04
% 6.59/2.33  Subsumption          : 0.40
% 6.59/2.33  Abstraction          : 0.05
% 6.59/2.33  MUC search           : 0.00
% 6.59/2.33  Cooper               : 0.00
% 6.59/2.33  Total                : 1.58
% 6.59/2.33  Index Insertion      : 0.00
% 6.59/2.33  Index Deletion       : 0.00
% 6.59/2.33  Index Matching       : 0.00
% 6.59/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
