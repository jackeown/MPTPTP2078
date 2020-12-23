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
% DateTime   : Thu Dec  3 10:25:36 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 279 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_129,plain,(
    ! [A_56] :
      ( r2_hidden(u1_struct_0(A_56),u1_pre_topc(A_56))
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,k3_tarski(B_4))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [B_35,A_36] :
      ( m1_setfam_1(B_35,A_36)
      | ~ r1_tarski(A_36,k3_tarski(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [B_4,A_3] :
      ( m1_setfam_1(B_4,A_3)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_136,plain,(
    ! [A_56] :
      ( m1_setfam_1(u1_pre_topc(A_56),u1_struct_0(A_56))
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_129,c_84])).

tff(c_62,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_234,plain,(
    ! [A_73,B_74] :
      ( k5_setfam_1(A_73,B_74) = A_73
      | ~ m1_setfam_1(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_316,plain,(
    ! [A_99] :
      ( k5_setfam_1(u1_struct_0(A_99),u1_pre_topc(A_99)) = u1_struct_0(A_99)
      | ~ m1_setfam_1(u1_pre_topc(A_99),u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_62,c_234])).

tff(c_325,plain,(
    ! [A_100] :
      ( k5_setfam_1(u1_struct_0(A_100),u1_pre_topc(A_100)) = u1_struct_0(A_100)
      | ~ v2_pre_topc(A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_136,c_316])).

tff(c_138,plain,(
    ! [A_58,B_59] :
      ( k5_setfam_1(A_58,B_59) = k3_tarski(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    ! [A_30] :
      ( k5_setfam_1(u1_struct_0(A_30),u1_pre_topc(A_30)) = k3_tarski(u1_pre_topc(A_30))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_62,c_138])).

tff(c_331,plain,(
    ! [A_100] :
      ( k3_tarski(u1_pre_topc(A_100)) = u1_struct_0(A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_146])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_499,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_121),B_122),u1_pre_topc(A_121))
      | ~ r1_tarski(B_122,u1_pre_topc(A_121))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121))))
      | ~ v2_pre_topc(A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_513,plain,(
    ! [A_30] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_30)),u1_pre_topc(A_30))
      | ~ r1_tarski(u1_pre_topc(A_30),u1_pre_topc(A_30))
      | ~ m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ v2_pre_topc(A_30)
      | ~ l1_pre_topc(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_499])).

tff(c_530,plain,(
    ! [A_124] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_124)),u1_pre_topc(A_124))
      | ~ m1_subset_1(u1_pre_topc(A_124),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124))))
      | ~ v2_pre_topc(A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_513])).

tff(c_539,plain,(
    ! [A_125] :
      ( r2_hidden(k3_tarski(u1_pre_topc(A_125)),u1_pre_topc(A_125))
      | ~ v2_pre_topc(A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_62,c_530])).

tff(c_64,plain,(
    ! [A_31] :
      ( k4_yellow_0(k2_yellow_1(A_31)) = k3_tarski(A_31)
      | ~ r2_hidden(k3_tarski(A_31),A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_611,plain,(
    ! [A_128] :
      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(A_128))) = k3_tarski(u1_pre_topc(A_128))
      | v1_xboole_0(u1_pre_topc(A_128))
      | ~ v2_pre_topc(A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_539,c_64])).

tff(c_66,plain,(
    k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4'))) != u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_617,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_66])).

tff(c_623,plain,
    ( k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4')
    | v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_617])).

tff(c_625,plain,(
    k3_tarski(u1_pre_topc('#skF_4')) != u1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_628,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_625])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_628])).

tff(c_633,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_127,plain,(
    ! [B_10,A_52,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_52,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_214,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | ~ r1_tarski(u1_pre_topc(A_72),B_71)
      | ~ v2_pre_topc(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_129,c_127])).

tff(c_233,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(u1_pre_topc(A_72))
      | ~ v2_pre_topc(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_637,plain,
    ( ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_633,c_233])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.08/1.47  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.08/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.47  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.08/1.47  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 3.08/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.08/1.48  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k4_yellow_0(k2_yellow_1(u1_pre_topc(A))) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 3.08/1.48  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.08/1.48  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.08/1.48  tff(f_39, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 3.08/1.48  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.08/1.48  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 3.08/1.48  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.08/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.48  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 3.08/1.48  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.08/1.48  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.08/1.48  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.48  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.48  tff(c_129, plain, (![A_56]: (r2_hidden(u1_struct_0(A_56), u1_pre_topc(A_56)) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.48  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k3_tarski(B_4)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.48  tff(c_76, plain, (![B_35, A_36]: (m1_setfam_1(B_35, A_36) | ~r1_tarski(A_36, k3_tarski(B_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.48  tff(c_84, plain, (![B_4, A_3]: (m1_setfam_1(B_4, A_3) | ~r2_hidden(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_76])).
% 3.08/1.48  tff(c_136, plain, (![A_56]: (m1_setfam_1(u1_pre_topc(A_56), u1_struct_0(A_56)) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_129, c_84])).
% 3.08/1.48  tff(c_62, plain, (![A_30]: (m1_subset_1(u1_pre_topc(A_30), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.48  tff(c_234, plain, (![A_73, B_74]: (k5_setfam_1(A_73, B_74)=A_73 | ~m1_setfam_1(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.48  tff(c_316, plain, (![A_99]: (k5_setfam_1(u1_struct_0(A_99), u1_pre_topc(A_99))=u1_struct_0(A_99) | ~m1_setfam_1(u1_pre_topc(A_99), u1_struct_0(A_99)) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_62, c_234])).
% 3.08/1.48  tff(c_325, plain, (![A_100]: (k5_setfam_1(u1_struct_0(A_100), u1_pre_topc(A_100))=u1_struct_0(A_100) | ~v2_pre_topc(A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_136, c_316])).
% 3.08/1.48  tff(c_138, plain, (![A_58, B_59]: (k5_setfam_1(A_58, B_59)=k3_tarski(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.48  tff(c_146, plain, (![A_30]: (k5_setfam_1(u1_struct_0(A_30), u1_pre_topc(A_30))=k3_tarski(u1_pre_topc(A_30)) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_62, c_138])).
% 3.08/1.48  tff(c_331, plain, (![A_100]: (k3_tarski(u1_pre_topc(A_100))=u1_struct_0(A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | ~l1_pre_topc(A_100))), inference(superposition, [status(thm), theory('equality')], [c_325, c_146])).
% 3.08/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.48  tff(c_499, plain, (![A_121, B_122]: (r2_hidden(k5_setfam_1(u1_struct_0(A_121), B_122), u1_pre_topc(A_121)) | ~r1_tarski(B_122, u1_pre_topc(A_121)) | ~m1_subset_1(B_122, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121)))) | ~v2_pre_topc(A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.08/1.48  tff(c_513, plain, (![A_30]: (r2_hidden(k3_tarski(u1_pre_topc(A_30)), u1_pre_topc(A_30)) | ~r1_tarski(u1_pre_topc(A_30), u1_pre_topc(A_30)) | ~m1_subset_1(u1_pre_topc(A_30), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~v2_pre_topc(A_30) | ~l1_pre_topc(A_30) | ~l1_pre_topc(A_30))), inference(superposition, [status(thm), theory('equality')], [c_146, c_499])).
% 3.08/1.48  tff(c_530, plain, (![A_124]: (r2_hidden(k3_tarski(u1_pre_topc(A_124)), u1_pre_topc(A_124)) | ~m1_subset_1(u1_pre_topc(A_124), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124)))) | ~v2_pre_topc(A_124) | ~l1_pre_topc(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_513])).
% 3.08/1.48  tff(c_539, plain, (![A_125]: (r2_hidden(k3_tarski(u1_pre_topc(A_125)), u1_pre_topc(A_125)) | ~v2_pre_topc(A_125) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_62, c_530])).
% 3.08/1.48  tff(c_64, plain, (![A_31]: (k4_yellow_0(k2_yellow_1(A_31))=k3_tarski(A_31) | ~r2_hidden(k3_tarski(A_31), A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.08/1.48  tff(c_611, plain, (![A_128]: (k4_yellow_0(k2_yellow_1(u1_pre_topc(A_128)))=k3_tarski(u1_pre_topc(A_128)) | v1_xboole_0(u1_pre_topc(A_128)) | ~v2_pre_topc(A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_539, c_64])).
% 3.08/1.48  tff(c_66, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc('#skF_4')))!=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.08/1.48  tff(c_617, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_611, c_66])).
% 3.08/1.48  tff(c_623, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4') | v1_xboole_0(u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_617])).
% 3.08/1.48  tff(c_625, plain, (k3_tarski(u1_pre_topc('#skF_4'))!=u1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_623])).
% 3.08/1.48  tff(c_628, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_331, c_625])).
% 3.08/1.48  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_628])).
% 3.08/1.48  tff(c_633, plain, (v1_xboole_0(u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_623])).
% 3.08/1.48  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.48  tff(c_121, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.08/1.48  tff(c_127, plain, (![B_10, A_52, A_9]: (~v1_xboole_0(B_10) | ~r2_hidden(A_52, A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_18, c_121])).
% 3.08/1.48  tff(c_214, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | ~r1_tarski(u1_pre_topc(A_72), B_71) | ~v2_pre_topc(A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_129, c_127])).
% 3.08/1.48  tff(c_233, plain, (![A_72]: (~v1_xboole_0(u1_pre_topc(A_72)) | ~v2_pre_topc(A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_6, c_214])).
% 3.08/1.48  tff(c_637, plain, (~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_633, c_233])).
% 3.08/1.48  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_637])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 120
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 1
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 19
% 3.08/1.48  #Demod        : 19
% 3.08/1.48  #Tautology    : 30
% 3.08/1.48  #SimpNegUnit  : 0
% 3.08/1.48  #BackRed      : 0
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.08/1.48  Preprocessing        : 0.35
% 3.08/1.48  Parsing              : 0.19
% 3.08/1.48  CNF conversion       : 0.02
% 3.08/1.48  Main loop            : 0.32
% 3.08/1.48  Inferencing          : 0.12
% 3.08/1.48  Reduction            : 0.08
% 3.08/1.48  Demodulation         : 0.06
% 3.08/1.48  BG Simplification    : 0.02
% 3.08/1.48  Subsumption          : 0.07
% 3.08/1.48  Abstraction          : 0.02
% 3.08/1.48  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.70
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
