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
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   60 (  81 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 221 expanded)
%              Number of equality atoms :   13 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_110,axiom,(
    ! [A] :
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,k1_tarski(B_5)) = A_4
      | r2_hidden(B_5,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_subset_1(A_43,B_44,C_45) = k4_xboole_0(B_44,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_128,plain,(
    ! [C_45] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',C_45) = k4_xboole_0('#skF_3',C_45) ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_215,plain,(
    ! [A_68,B_69] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68))),B_69,k1_tarski(k1_xboole_0)) = k2_yellow19(A_68,k3_yellow19(A_68,k2_struct_0(A_68),B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68)))))
      | ~ v13_waybel_0(B_69,k3_yellow_1(k2_struct_0(A_68)))
      | ~ v2_waybel_0(B_69,k3_yellow_1(k2_struct_0(A_68)))
      | v1_xboole_0(B_69)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_217,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))),'#skF_3',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_215])).

tff(c_223,plain,
    ( k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_128,c_217])).

tff(c_224,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) = k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_223])).

tff(c_38,plain,(
    k2_yellow19('#skF_2',k3_yellow19('#skF_2',k2_struct_0('#skF_2'),'#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_226,plain,(
    k4_xboole_0('#skF_3',k1_tarski(k1_xboole_0)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_38])).

tff(c_234,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_226])).

tff(c_36,plain,(
    ! [C_23,B_21,A_17] :
      ( ~ v1_xboole_0(C_23)
      | ~ r2_hidden(C_23,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17))))
      | ~ v13_waybel_0(B_21,k3_yellow_1(A_17))
      | ~ v2_waybel_0(B_21,k3_yellow_1(A_17))
      | ~ v1_subset_1(B_21,u1_struct_0(k3_yellow_1(A_17)))
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_236,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_17))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_17))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_17)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_234,c_36])).

tff(c_242,plain,(
    ! [A_17] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_17))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_17))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_17)))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_245,plain,(
    ! [A_70] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_70))))
      | ~ v13_waybel_0('#skF_3',k3_yellow_1(A_70))
      | ~ v2_waybel_0('#skF_3',k3_yellow_1(A_70))
      | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(A_70)))
      | v1_xboole_0(A_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_242])).

tff(c_248,plain,
    ( ~ v13_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v2_waybel_0('#skF_3',k3_yellow_1(k2_struct_0('#skF_2')))
    | ~ v1_subset_1('#skF_3',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_245])).

tff(c_254,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_248])).

tff(c_32,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_265,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_254,c_32])).

tff(c_269,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_265])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.33  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.17/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.33  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.17/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.33  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.17/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.33  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.17/1.33  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.17/1.33  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.17/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.17/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.33  
% 2.49/1.35  tff(f_130, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 2.49/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.49/1.35  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.49/1.35  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.49/1.35  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 2.49/1.35  tff(f_110, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 2.49/1.35  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.49/1.35  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_50, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_46, plain, (v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_44, plain, (v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_42, plain, (v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.49/1.35  tff(c_18, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k1_tarski(B_5))=A_4 | r2_hidden(B_5, A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.35  tff(c_120, plain, (![A_43, B_44, C_45]: (k7_subset_1(A_43, B_44, C_45)=k4_xboole_0(B_44, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.35  tff(c_128, plain, (![C_45]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', C_45)=k4_xboole_0('#skF_3', C_45))), inference(resolution, [status(thm)], [c_40, c_120])).
% 2.49/1.35  tff(c_215, plain, (![A_68, B_69]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68))), B_69, k1_tarski(k1_xboole_0))=k2_yellow19(A_68, k3_yellow19(A_68, k2_struct_0(A_68), B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68))))) | ~v13_waybel_0(B_69, k3_yellow_1(k2_struct_0(A_68))) | ~v2_waybel_0(B_69, k3_yellow_1(k2_struct_0(A_68))) | v1_xboole_0(B_69) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.49/1.35  tff(c_217, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2'))), '#skF_3', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3')) | ~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_215])).
% 2.49/1.35  tff(c_223, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_128, c_217])).
% 2.49/1.35  tff(c_224, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))=k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_223])).
% 2.49/1.35  tff(c_38, plain, (k2_yellow19('#skF_2', k3_yellow19('#skF_2', k2_struct_0('#skF_2'), '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.49/1.35  tff(c_226, plain, (k4_xboole_0('#skF_3', k1_tarski(k1_xboole_0))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_38])).
% 2.49/1.35  tff(c_234, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_226])).
% 2.49/1.35  tff(c_36, plain, (![C_23, B_21, A_17]: (~v1_xboole_0(C_23) | ~r2_hidden(C_23, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17)))) | ~v13_waybel_0(B_21, k3_yellow_1(A_17)) | ~v2_waybel_0(B_21, k3_yellow_1(A_17)) | ~v1_subset_1(B_21, u1_struct_0(k3_yellow_1(A_17))) | v1_xboole_0(B_21) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.49/1.35  tff(c_236, plain, (![A_17]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_17)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_17)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_17))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_234, c_36])).
% 2.49/1.35  tff(c_242, plain, (![A_17]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_17)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_17)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_17)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_17))) | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_236])).
% 2.49/1.35  tff(c_245, plain, (![A_70]: (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_70)))) | ~v13_waybel_0('#skF_3', k3_yellow_1(A_70)) | ~v2_waybel_0('#skF_3', k3_yellow_1(A_70)) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(A_70))) | v1_xboole_0(A_70))), inference(negUnitSimplification, [status(thm)], [c_48, c_242])).
% 2.49/1.35  tff(c_248, plain, (~v13_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v2_waybel_0('#skF_3', k3_yellow_1(k2_struct_0('#skF_2'))) | ~v1_subset_1('#skF_3', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_2')))) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_245])).
% 2.49/1.35  tff(c_254, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_248])).
% 2.49/1.35  tff(c_32, plain, (![A_13]: (~v1_xboole_0(k2_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.35  tff(c_265, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_254, c_32])).
% 2.49/1.35  tff(c_269, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_265])).
% 2.49/1.35  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_269])).
% 2.49/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  Inference rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Ref     : 0
% 2.49/1.35  #Sup     : 50
% 2.49/1.35  #Fact    : 0
% 2.49/1.35  #Define  : 0
% 2.49/1.35  #Split   : 1
% 2.49/1.35  #Chain   : 0
% 2.49/1.35  #Close   : 0
% 2.49/1.35  
% 2.49/1.35  Ordering : KBO
% 2.49/1.35  
% 2.49/1.35  Simplification rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Subsume      : 5
% 2.49/1.35  #Demod        : 11
% 2.49/1.35  #Tautology    : 22
% 2.49/1.35  #SimpNegUnit  : 4
% 2.49/1.35  #BackRed      : 1
% 2.49/1.35  
% 2.49/1.35  #Partial instantiations: 0
% 2.49/1.35  #Strategies tried      : 1
% 2.49/1.35  
% 2.49/1.35  Timing (in seconds)
% 2.49/1.35  ----------------------
% 2.49/1.35  Preprocessing        : 0.32
% 2.49/1.35  Parsing              : 0.16
% 2.49/1.35  CNF conversion       : 0.02
% 2.49/1.35  Main loop            : 0.21
% 2.49/1.35  Inferencing          : 0.08
% 2.49/1.35  Reduction            : 0.06
% 2.49/1.35  Demodulation         : 0.04
% 2.49/1.35  BG Simplification    : 0.02
% 2.49/1.35  Subsumption          : 0.04
% 2.49/1.35  Abstraction          : 0.01
% 2.49/1.35  MUC search           : 0.00
% 2.49/1.35  Cooper               : 0.00
% 2.49/1.35  Total                : 0.56
% 2.49/1.35  Index Insertion      : 0.00
% 2.49/1.35  Index Deletion       : 0.00
% 2.49/1.35  Index Matching       : 0.00
% 2.49/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
