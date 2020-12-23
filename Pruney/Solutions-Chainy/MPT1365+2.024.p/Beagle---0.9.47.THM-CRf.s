%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 6.78s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 355 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_121,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,C_83) = k3_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [B_82] : k9_subset_1(u1_struct_0('#skF_1'),B_82,'#skF_3') = k3_xboole_0(B_82,'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_34,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_175,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_34])).

tff(c_70,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_365,plain,(
    ! [B_131,A_132] :
      ( v4_pre_topc(B_131,A_132)
      | ~ v2_compts_1(B_131,A_132)
      | ~ v8_pre_topc(A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_396,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_365])).

tff(c_422,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_36,c_396])).

tff(c_38,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_399,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_365])).

tff(c_425,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_38,c_399])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_588,plain,(
    ! [B_170,C_171,A_172] :
      ( v4_pre_topc(k3_xboole_0(B_170,C_171),A_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v4_pre_topc(C_171,A_172)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v4_pre_topc(B_170,A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1108,plain,(
    ! [B_226,A_227,A_228] :
      ( v4_pre_topc(k3_xboole_0(B_226,A_227),A_228)
      | ~ v4_pre_topc(A_227,A_228)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ v4_pre_topc(B_226,A_228)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | ~ r1_tarski(A_227,u1_struct_0(A_228)) ) ),
    inference(resolution,[status(thm)],[c_26,c_588])).

tff(c_1139,plain,(
    ! [A_227] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_227),'#skF_1')
      | ~ v4_pre_topc(A_227,'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_227,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1108])).

tff(c_1171,plain,(
    ! [A_227] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_227),'#skF_1')
      | ~ v4_pre_topc(A_227,'#skF_1')
      | ~ r1_tarski(A_227,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_425,c_1139])).

tff(c_176,plain,(
    ! [B_95] : k9_subset_1(u1_struct_0('#skF_1'),B_95,'#skF_3') = k3_xboole_0(B_95,'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_18,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k9_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [B_95] :
      ( m1_subset_1(k3_xboole_0(B_95,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_18])).

tff(c_193,plain,(
    ! [B_95] : m1_subset_1(k3_xboole_0(B_95,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_185])).

tff(c_14,plain,(
    ! [A_28] : k2_subset_1(A_28) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_137,plain,(
    ! [A_84,B_85] : k9_subset_1(A_84,B_85,A_84) = k3_xboole_0(B_85,A_84) ),
    inference(resolution,[status(thm)],[c_49,c_121])).

tff(c_106,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1(k9_subset_1(A_71,B_72,C_73),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_110,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k9_subset_1(A_71,B_72,C_73),A_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_106,c_24])).

tff(c_143,plain,(
    ! [B_85,A_84] :
      ( r1_tarski(k3_xboole_0(B_85,A_84),A_84)
      | ~ m1_subset_1(A_84,k1_zfmisc_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_110])).

tff(c_152,plain,(
    ! [B_85,A_84] : r1_tarski(k3_xboole_0(B_85,A_84),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_143])).

tff(c_781,plain,(
    ! [C_175,A_176,B_177] :
      ( v2_compts_1(C_175,A_176)
      | ~ v4_pre_topc(C_175,A_176)
      | ~ r1_tarski(C_175,B_177)
      | ~ v2_compts_1(B_177,A_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3811,plain,(
    ! [B_573,A_574,A_575] :
      ( v2_compts_1(k3_xboole_0(B_573,A_574),A_575)
      | ~ v4_pre_topc(k3_xboole_0(B_573,A_574),A_575)
      | ~ v2_compts_1(A_574,A_575)
      | ~ m1_subset_1(k3_xboole_0(B_573,A_574),k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ m1_subset_1(A_574,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575) ) ),
    inference(resolution,[status(thm)],[c_152,c_781])).

tff(c_3875,plain,(
    ! [B_95] :
      ( v2_compts_1(k3_xboole_0(B_95,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_95,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_193,c_3811])).

tff(c_4092,plain,(
    ! [B_577] :
      ( v2_compts_1(k3_xboole_0(B_577,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_577,'#skF_3'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_36,c_3875])).

tff(c_4159,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1171,c_4092])).

tff(c_4229,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_422,c_4159])).

tff(c_4231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_4229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.78/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.78/2.49  
% 6.78/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.78/2.50  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.78/2.50  
% 6.78/2.50  %Foreground sorts:
% 6.78/2.50  
% 6.78/2.50  
% 6.78/2.50  %Background operators:
% 6.78/2.50  
% 6.78/2.50  
% 6.78/2.50  %Foreground operators:
% 6.78/2.50  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 6.78/2.50  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 6.78/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.78/2.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.78/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.78/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.78/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.78/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.78/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.78/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.78/2.50  tff('#skF_3', type, '#skF_3': $i).
% 6.78/2.50  tff('#skF_1', type, '#skF_1': $i).
% 6.78/2.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.78/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.78/2.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.78/2.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.78/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.78/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.78/2.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.78/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.78/2.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.78/2.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.78/2.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.78/2.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.78/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.78/2.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.78/2.50  
% 7.05/2.52  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 7.05/2.52  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.05/2.52  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.05/2.52  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 7.05/2.52  tff(f_69, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 7.05/2.52  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.05/2.52  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.05/2.52  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.05/2.52  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 7.05/2.52  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_121, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, C_83)=k3_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.05/2.52  tff(c_134, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_1'), B_82, '#skF_3')=k3_xboole_0(B_82, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_121])).
% 7.05/2.52  tff(c_34, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_175, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_34])).
% 7.05/2.52  tff(c_70, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.05/2.52  tff(c_84, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 7.05/2.52  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_40, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_36, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_365, plain, (![B_131, A_132]: (v4_pre_topc(B_131, A_132) | ~v2_compts_1(B_131, A_132) | ~v8_pre_topc(A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.05/2.52  tff(c_396, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_365])).
% 7.05/2.52  tff(c_422, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_36, c_396])).
% 7.05/2.52  tff(c_38, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.05/2.52  tff(c_399, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_365])).
% 7.05/2.52  tff(c_425, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_38, c_399])).
% 7.05/2.52  tff(c_26, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.05/2.52  tff(c_588, plain, (![B_170, C_171, A_172]: (v4_pre_topc(k3_xboole_0(B_170, C_171), A_172) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~v4_pre_topc(C_171, A_172) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_172))) | ~v4_pre_topc(B_170, A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.05/2.52  tff(c_1108, plain, (![B_226, A_227, A_228]: (v4_pre_topc(k3_xboole_0(B_226, A_227), A_228) | ~v4_pre_topc(A_227, A_228) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_228))) | ~v4_pre_topc(B_226, A_228) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | ~r1_tarski(A_227, u1_struct_0(A_228)))), inference(resolution, [status(thm)], [c_26, c_588])).
% 7.05/2.52  tff(c_1139, plain, (![A_227]: (v4_pre_topc(k3_xboole_0('#skF_2', A_227), '#skF_1') | ~v4_pre_topc(A_227, '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_227, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_1108])).
% 7.05/2.52  tff(c_1171, plain, (![A_227]: (v4_pre_topc(k3_xboole_0('#skF_2', A_227), '#skF_1') | ~v4_pre_topc(A_227, '#skF_1') | ~r1_tarski(A_227, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_425, c_1139])).
% 7.05/2.52  tff(c_176, plain, (![B_95]: (k9_subset_1(u1_struct_0('#skF_1'), B_95, '#skF_3')=k3_xboole_0(B_95, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_121])).
% 7.05/2.52  tff(c_18, plain, (![A_30, B_31, C_32]: (m1_subset_1(k9_subset_1(A_30, B_31, C_32), k1_zfmisc_1(A_30)) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.05/2.52  tff(c_185, plain, (![B_95]: (m1_subset_1(k3_xboole_0(B_95, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_176, c_18])).
% 7.05/2.52  tff(c_193, plain, (![B_95]: (m1_subset_1(k3_xboole_0(B_95, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_185])).
% 7.05/2.52  tff(c_14, plain, (![A_28]: (k2_subset_1(A_28)=A_28)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.05/2.52  tff(c_16, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.05/2.52  tff(c_49, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 7.05/2.52  tff(c_137, plain, (![A_84, B_85]: (k9_subset_1(A_84, B_85, A_84)=k3_xboole_0(B_85, A_84))), inference(resolution, [status(thm)], [c_49, c_121])).
% 7.05/2.52  tff(c_106, plain, (![A_71, B_72, C_73]: (m1_subset_1(k9_subset_1(A_71, B_72, C_73), k1_zfmisc_1(A_71)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.05/2.52  tff(c_24, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.05/2.52  tff(c_110, plain, (![A_71, B_72, C_73]: (r1_tarski(k9_subset_1(A_71, B_72, C_73), A_71) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_106, c_24])).
% 7.05/2.52  tff(c_143, plain, (![B_85, A_84]: (r1_tarski(k3_xboole_0(B_85, A_84), A_84) | ~m1_subset_1(A_84, k1_zfmisc_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_110])).
% 7.05/2.52  tff(c_152, plain, (![B_85, A_84]: (r1_tarski(k3_xboole_0(B_85, A_84), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_143])).
% 7.05/2.52  tff(c_781, plain, (![C_175, A_176, B_177]: (v2_compts_1(C_175, A_176) | ~v4_pre_topc(C_175, A_176) | ~r1_tarski(C_175, B_177) | ~v2_compts_1(B_177, A_176) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.05/2.52  tff(c_3811, plain, (![B_573, A_574, A_575]: (v2_compts_1(k3_xboole_0(B_573, A_574), A_575) | ~v4_pre_topc(k3_xboole_0(B_573, A_574), A_575) | ~v2_compts_1(A_574, A_575) | ~m1_subset_1(k3_xboole_0(B_573, A_574), k1_zfmisc_1(u1_struct_0(A_575))) | ~m1_subset_1(A_574, k1_zfmisc_1(u1_struct_0(A_575))) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575))), inference(resolution, [status(thm)], [c_152, c_781])).
% 7.05/2.52  tff(c_3875, plain, (![B_95]: (v2_compts_1(k3_xboole_0(B_95, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_95, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_193, c_3811])).
% 7.05/2.52  tff(c_4092, plain, (![B_577]: (v2_compts_1(k3_xboole_0(B_577, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_577, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_36, c_3875])).
% 7.05/2.52  tff(c_4159, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1171, c_4092])).
% 7.05/2.52  tff(c_4229, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_422, c_4159])).
% 7.05/2.52  tff(c_4231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_4229])).
% 7.05/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.52  
% 7.05/2.52  Inference rules
% 7.05/2.52  ----------------------
% 7.05/2.52  #Ref     : 0
% 7.05/2.52  #Sup     : 879
% 7.05/2.52  #Fact    : 0
% 7.05/2.52  #Define  : 0
% 7.05/2.52  #Split   : 1
% 7.05/2.52  #Chain   : 0
% 7.05/2.52  #Close   : 0
% 7.05/2.52  
% 7.05/2.52  Ordering : KBO
% 7.05/2.52  
% 7.05/2.52  Simplification rules
% 7.05/2.52  ----------------------
% 7.05/2.52  #Subsume      : 98
% 7.05/2.52  #Demod        : 1471
% 7.05/2.52  #Tautology    : 230
% 7.05/2.52  #SimpNegUnit  : 1
% 7.05/2.52  #BackRed      : 1
% 7.05/2.52  
% 7.05/2.52  #Partial instantiations: 0
% 7.05/2.52  #Strategies tried      : 1
% 7.05/2.52  
% 7.05/2.52  Timing (in seconds)
% 7.05/2.52  ----------------------
% 7.05/2.53  Preprocessing        : 0.38
% 7.05/2.53  Parsing              : 0.20
% 7.05/2.53  CNF conversion       : 0.03
% 7.05/2.53  Main loop            : 1.29
% 7.05/2.53  Inferencing          : 0.44
% 7.05/2.53  Reduction            : 0.51
% 7.05/2.53  Demodulation         : 0.41
% 7.05/2.53  BG Simplification    : 0.05
% 7.05/2.53  Subsumption          : 0.23
% 7.05/2.53  Abstraction          : 0.07
% 7.05/2.53  MUC search           : 0.00
% 7.05/2.53  Cooper               : 0.00
% 7.05/2.53  Total                : 1.72
% 7.05/2.53  Index Insertion      : 0.00
% 7.05/2.53  Index Deletion       : 0.00
% 7.05/2.53  Index Matching       : 0.00
% 7.05/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
