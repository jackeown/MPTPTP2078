%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 194 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 585 expanded)
%              Number of equality atoms :    6 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_115,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_96,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_155,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_26,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_165,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_26])).

tff(c_53,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_276,plain,(
    ! [B_68,A_69] :
      ( v4_pre_topc(B_68,A_69)
      | ~ v2_compts_1(B_68,A_69)
      | ~ v8_pre_topc(A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_290,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_276])).

tff(c_301,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_28,c_290])).

tff(c_30,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_293,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_276])).

tff(c_304,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_30,c_293])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_461,plain,(
    ! [B_83,C_84,A_85] :
      ( v4_pre_topc(k3_xboole_0(B_83,C_84),A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v4_pre_topc(C_84,A_85)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v4_pre_topc(B_83,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1076,plain,(
    ! [B_144,A_145,A_146] :
      ( v4_pre_topc(k3_xboole_0(B_144,A_145),A_146)
      | ~ v4_pre_topc(A_145,A_146)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v4_pre_topc(B_144,A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | ~ r1_tarski(A_145,u1_struct_0(A_146)) ) ),
    inference(resolution,[status(thm)],[c_18,c_461])).

tff(c_1097,plain,(
    ! [A_145] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_145),'#skF_1')
      | ~ v4_pre_topc(A_145,'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_145,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1076])).

tff(c_1118,plain,(
    ! [A_145] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_145),'#skF_1')
      | ~ v4_pre_topc(A_145,'#skF_1')
      | ~ r1_tarski(A_145,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_304,c_1097])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_229,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k9_subset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [B_52] :
      ( m1_subset_1(k3_xboole_0(B_52,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_229])).

tff(c_249,plain,(
    ! [B_52] : m1_subset_1(k3_xboole_0(B_52,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_243])).

tff(c_202,plain,(
    ! [B_58,B_59,A_60] :
      ( k9_subset_1(B_58,B_59,A_60) = k3_xboole_0(B_59,A_60)
      | ~ r1_tarski(A_60,B_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_219,plain,(
    ! [B_2,B_59] : k9_subset_1(B_2,B_59,B_2) = k3_xboole_0(B_59,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k9_subset_1(A_63,B_64,C_65),A_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_229,c_16])).

tff(c_600,plain,(
    ! [C_95,A_96,B_97] :
      ( v2_compts_1(C_95,A_96)
      | ~ v4_pre_topc(C_95,A_96)
      | ~ r1_tarski(C_95,B_97)
      | ~ v2_compts_1(B_97,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3498,plain,(
    ! [A_370,B_371,C_372,A_373] :
      ( v2_compts_1(k9_subset_1(A_370,B_371,C_372),A_373)
      | ~ v4_pre_topc(k9_subset_1(A_370,B_371,C_372),A_373)
      | ~ v2_compts_1(A_370,A_373)
      | ~ m1_subset_1(k9_subset_1(A_370,B_371,C_372),k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ m1_subset_1(A_370,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(A_370)) ) ),
    inference(resolution,[status(thm)],[c_245,c_600])).

tff(c_3538,plain,(
    ! [B_2,B_59,A_373] :
      ( v2_compts_1(k9_subset_1(B_2,B_59,B_2),A_373)
      | ~ v4_pre_topc(k9_subset_1(B_2,B_59,B_2),A_373)
      | ~ v2_compts_1(B_2,A_373)
      | ~ m1_subset_1(k3_xboole_0(B_59,B_2),k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_3498])).

tff(c_15845,plain,(
    ! [B_938,B_939,A_940] :
      ( v2_compts_1(k3_xboole_0(B_938,B_939),A_940)
      | ~ v4_pre_topc(k3_xboole_0(B_938,B_939),A_940)
      | ~ v2_compts_1(B_939,A_940)
      | ~ m1_subset_1(k3_xboole_0(B_938,B_939),k1_zfmisc_1(u1_struct_0(A_940)))
      | ~ m1_subset_1(B_939,k1_zfmisc_1(u1_struct_0(A_940)))
      | ~ l1_pre_topc(A_940)
      | ~ v2_pre_topc(A_940)
      | ~ m1_subset_1(B_939,k1_zfmisc_1(B_939)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_219,c_3538])).

tff(c_15892,plain,(
    ! [B_52] :
      ( v2_compts_1(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_249,c_15845])).

tff(c_15941,plain,(
    ! [B_52] :
      ( v2_compts_1(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_52,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_28,c_15892])).

tff(c_15946,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15941])).

tff(c_15949,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_15946])).

tff(c_15953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15949])).

tff(c_16104,plain,(
    ! [B_943] :
      ( v2_compts_1(k3_xboole_0(B_943,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_943,'#skF_3'),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_15941])).

tff(c_16187,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1118,c_16104])).

tff(c_16254,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_301,c_16187])).

tff(c_16256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_16254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.83/4.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/4.90  
% 11.83/4.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/4.91  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 11.83/4.91  
% 11.83/4.91  %Foreground sorts:
% 11.83/4.91  
% 11.83/4.91  
% 11.83/4.91  %Background operators:
% 11.83/4.91  
% 11.83/4.91  
% 11.83/4.91  %Foreground operators:
% 11.83/4.91  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 11.83/4.91  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 11.83/4.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.83/4.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.83/4.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.83/4.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.83/4.91  tff('#skF_2', type, '#skF_2': $i).
% 11.83/4.91  tff('#skF_3', type, '#skF_3': $i).
% 11.83/4.91  tff('#skF_1', type, '#skF_1': $i).
% 11.83/4.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.83/4.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.83/4.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.83/4.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.83/4.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.83/4.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.83/4.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.83/4.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.83/4.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.83/4.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.83/4.91  
% 11.83/4.92  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 11.83/4.92  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.83/4.92  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.83/4.92  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 11.83/4.92  tff(f_65, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 11.83/4.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.83/4.92  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 11.83/4.92  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 11.83/4.92  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_155, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.83/4.92  tff(c_163, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_155])).
% 11.83/4.92  tff(c_26, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_165, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_26])).
% 11.83/4.92  tff(c_53, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.83/4.92  tff(c_64, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_53])).
% 11.83/4.92  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_32, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_28, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_276, plain, (![B_68, A_69]: (v4_pre_topc(B_68, A_69) | ~v2_compts_1(B_68, A_69) | ~v8_pre_topc(A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.83/4.92  tff(c_290, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_276])).
% 11.83/4.92  tff(c_301, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_28, c_290])).
% 11.83/4.92  tff(c_30, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.83/4.92  tff(c_293, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_276])).
% 11.83/4.92  tff(c_304, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_30, c_293])).
% 11.83/4.92  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.83/4.92  tff(c_461, plain, (![B_83, C_84, A_85]: (v4_pre_topc(k3_xboole_0(B_83, C_84), A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~v4_pre_topc(C_84, A_85) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_85))) | ~v4_pre_topc(B_83, A_85) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.83/4.92  tff(c_1076, plain, (![B_144, A_145, A_146]: (v4_pre_topc(k3_xboole_0(B_144, A_145), A_146) | ~v4_pre_topc(A_145, A_146) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_146))) | ~v4_pre_topc(B_144, A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | ~r1_tarski(A_145, u1_struct_0(A_146)))), inference(resolution, [status(thm)], [c_18, c_461])).
% 11.83/4.92  tff(c_1097, plain, (![A_145]: (v4_pre_topc(k3_xboole_0('#skF_2', A_145), '#skF_1') | ~v4_pre_topc(A_145, '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_145, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_1076])).
% 11.83/4.92  tff(c_1118, plain, (![A_145]: (v4_pre_topc(k3_xboole_0('#skF_2', A_145), '#skF_1') | ~v4_pre_topc(A_145, '#skF_1') | ~r1_tarski(A_145, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_304, c_1097])).
% 11.83/4.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.83/4.92  tff(c_229, plain, (![A_63, B_64, C_65]: (m1_subset_1(k9_subset_1(A_63, B_64, C_65), k1_zfmisc_1(A_63)) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.83/4.92  tff(c_243, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_163, c_229])).
% 11.83/4.92  tff(c_249, plain, (![B_52]: (m1_subset_1(k3_xboole_0(B_52, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_243])).
% 11.83/4.92  tff(c_202, plain, (![B_58, B_59, A_60]: (k9_subset_1(B_58, B_59, A_60)=k3_xboole_0(B_59, A_60) | ~r1_tarski(A_60, B_58))), inference(resolution, [status(thm)], [c_18, c_155])).
% 11.83/4.92  tff(c_219, plain, (![B_2, B_59]: (k9_subset_1(B_2, B_59, B_2)=k3_xboole_0(B_59, B_2))), inference(resolution, [status(thm)], [c_6, c_202])).
% 11.83/4.92  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.83/4.92  tff(c_245, plain, (![A_63, B_64, C_65]: (r1_tarski(k9_subset_1(A_63, B_64, C_65), A_63) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_229, c_16])).
% 11.83/4.92  tff(c_600, plain, (![C_95, A_96, B_97]: (v2_compts_1(C_95, A_96) | ~v4_pre_topc(C_95, A_96) | ~r1_tarski(C_95, B_97) | ~v2_compts_1(B_97, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.83/4.92  tff(c_3498, plain, (![A_370, B_371, C_372, A_373]: (v2_compts_1(k9_subset_1(A_370, B_371, C_372), A_373) | ~v4_pre_topc(k9_subset_1(A_370, B_371, C_372), A_373) | ~v2_compts_1(A_370, A_373) | ~m1_subset_1(k9_subset_1(A_370, B_371, C_372), k1_zfmisc_1(u1_struct_0(A_373))) | ~m1_subset_1(A_370, k1_zfmisc_1(u1_struct_0(A_373))) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | ~m1_subset_1(C_372, k1_zfmisc_1(A_370)))), inference(resolution, [status(thm)], [c_245, c_600])).
% 11.83/4.92  tff(c_3538, plain, (![B_2, B_59, A_373]: (v2_compts_1(k9_subset_1(B_2, B_59, B_2), A_373) | ~v4_pre_topc(k9_subset_1(B_2, B_59, B_2), A_373) | ~v2_compts_1(B_2, A_373) | ~m1_subset_1(k3_xboole_0(B_59, B_2), k1_zfmisc_1(u1_struct_0(A_373))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_373))) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_3498])).
% 11.83/4.92  tff(c_15845, plain, (![B_938, B_939, A_940]: (v2_compts_1(k3_xboole_0(B_938, B_939), A_940) | ~v4_pre_topc(k3_xboole_0(B_938, B_939), A_940) | ~v2_compts_1(B_939, A_940) | ~m1_subset_1(k3_xboole_0(B_938, B_939), k1_zfmisc_1(u1_struct_0(A_940))) | ~m1_subset_1(B_939, k1_zfmisc_1(u1_struct_0(A_940))) | ~l1_pre_topc(A_940) | ~v2_pre_topc(A_940) | ~m1_subset_1(B_939, k1_zfmisc_1(B_939)))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_219, c_3538])).
% 11.83/4.92  tff(c_15892, plain, (![B_52]: (v2_compts_1(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_249, c_15845])).
% 11.83/4.92  tff(c_15941, plain, (![B_52]: (v2_compts_1(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_52, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_28, c_15892])).
% 11.83/4.92  tff(c_15946, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15941])).
% 11.83/4.92  tff(c_15949, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_15946])).
% 11.83/4.92  tff(c_15953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_15949])).
% 11.83/4.92  tff(c_16104, plain, (![B_943]: (v2_compts_1(k3_xboole_0(B_943, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_943, '#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_15941])).
% 11.83/4.92  tff(c_16187, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1118, c_16104])).
% 11.83/4.92  tff(c_16254, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_301, c_16187])).
% 11.83/4.92  tff(c_16256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_16254])).
% 11.83/4.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/4.92  
% 11.83/4.92  Inference rules
% 11.83/4.92  ----------------------
% 11.83/4.92  #Ref     : 0
% 11.83/4.92  #Sup     : 3967
% 11.83/4.92  #Fact    : 0
% 11.83/4.92  #Define  : 0
% 11.83/4.92  #Split   : 6
% 11.83/4.92  #Chain   : 0
% 11.83/4.92  #Close   : 0
% 11.83/4.92  
% 11.83/4.92  Ordering : KBO
% 11.83/4.92  
% 11.83/4.92  Simplification rules
% 11.83/4.92  ----------------------
% 11.83/4.92  #Subsume      : 1049
% 11.83/4.92  #Demod        : 2244
% 11.83/4.92  #Tautology    : 519
% 11.83/4.92  #SimpNegUnit  : 3
% 11.83/4.92  #BackRed      : 1
% 11.83/4.92  
% 11.83/4.92  #Partial instantiations: 0
% 11.83/4.92  #Strategies tried      : 1
% 11.83/4.92  
% 11.83/4.92  Timing (in seconds)
% 11.83/4.92  ----------------------
% 11.83/4.92  Preprocessing        : 0.32
% 11.83/4.92  Parsing              : 0.17
% 11.83/4.92  CNF conversion       : 0.02
% 11.83/4.92  Main loop            : 3.84
% 11.83/4.92  Inferencing          : 0.91
% 11.83/4.92  Reduction            : 1.27
% 11.83/4.92  Demodulation         : 1.00
% 11.83/4.92  BG Simplification    : 0.10
% 11.83/4.92  Subsumption          : 1.37
% 11.83/4.92  Abstraction          : 0.14
% 11.83/4.92  MUC search           : 0.00
% 11.83/4.92  Cooper               : 0.00
% 11.83/4.92  Total                : 4.18
% 11.83/4.92  Index Insertion      : 0.00
% 11.83/4.92  Index Deletion       : 0.00
% 11.83/4.92  Index Matching       : 0.00
% 11.83/4.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
