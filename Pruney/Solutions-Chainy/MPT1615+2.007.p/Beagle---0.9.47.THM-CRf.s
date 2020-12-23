%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:35 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 210 expanded)
%              Number of leaves         :   40 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 342 expanded)
%              Number of equality atoms :   16 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_100,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_76,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [A_68,B_69] :
      ( k5_setfam_1(A_68,B_69) = k3_tarski(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_210,plain,(
    ! [A_68] : k5_setfam_1(A_68,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_245,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k5_setfam_1(A_79,B_80),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_257,plain,(
    ! [A_68] :
      ( m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_245])).

tff(c_263,plain,(
    ! [A_81] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_257])).

tff(c_30,plain,(
    ! [A_20,C_22,B_21] :
      ( m1_subset_1(A_20,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_291,plain,(
    ! [A_83,A_84] :
      ( m1_subset_1(A_83,A_84)
      | ~ r2_hidden(A_83,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_263,c_30])).

tff(c_302,plain,(
    ! [A_84] :
      ( m1_subset_1('#skF_1'(k3_tarski(k1_xboole_0)),A_84)
      | v1_xboole_0(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_291])).

tff(c_338,plain,(
    v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_83,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_2'(A_46),A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_342,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_338,c_91])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( k5_setfam_1(A_16,B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,(
    ! [A_16] : k5_setfam_1(A_16,k3_tarski(k1_xboole_0)) = k3_tarski(k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_263,c_26])).

tff(c_345,plain,(
    ! [A_16] : k5_setfam_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_342,c_275])).

tff(c_714,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_148),B_149),u1_pre_topc(A_148))
      | ~ r1_tarski(B_149,u1_pre_topc(A_148))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ v2_pre_topc(A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_724,plain,(
    ! [A_148] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_148))
      | ~ r1_tarski(k1_xboole_0,u1_pre_topc(A_148))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ v2_pre_topc(A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_714])).

tff(c_729,plain,(
    ! [A_150] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_150))
      | ~ v2_pre_topc(A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8,c_724])).

tff(c_160,plain,(
    ! [A_61] :
      ( k3_yellow_0(k2_yellow_1(A_61)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_72,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_8'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_171,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_8'))
    | v1_xboole_0(u1_pre_topc('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_72])).

tff(c_173,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_732,plain,
    ( ~ v2_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_729,c_173])).

tff(c_742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_732])).

tff(c_744,plain,(
    ~ v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_146,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(A_59,B_60)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_157,plain,(
    ! [A_59,A_8] :
      ( r1_tarski(A_59,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_59,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_276,plain,(
    ! [A_82] :
      ( r1_tarski(k3_tarski(k1_xboole_0),A_82)
      | v1_xboole_0(k1_zfmisc_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_263,c_157])).

tff(c_92,plain,(
    ! [A_47] :
      ( v1_xboole_0(A_47)
      | r2_hidden('#skF_1'(A_47),A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    ! [A_47] :
      ( ~ r1_tarski(A_47,'#skF_1'(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_92,c_32])).

tff(c_290,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1('#skF_1'(k3_tarski(k1_xboole_0)))) ),
    inference(resolution,[status(thm)],[c_276,c_99])).

tff(c_760,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1'(k3_tarski(k1_xboole_0)))) ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_290])).

tff(c_120,plain,(
    ! [C_51,A_52] :
      ( r2_hidden(C_51,k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_51,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [A_52,C_51] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_52))
      | ~ r1_tarski(C_51,A_52) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_768,plain,(
    ! [C_152] : ~ r1_tarski(C_152,'#skF_1'(k3_tarski(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_760,c_128])).

tff(c_790,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_768])).

tff(c_791,plain,(
    v1_xboole_0(u1_pre_topc('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_805,plain,(
    u1_pre_topc('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_791,c_91])).

tff(c_792,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_818,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_792])).

tff(c_821,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_818,c_32])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:32:04 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.43  
% 2.89/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3 > #skF_8 > #skF_6 > #skF_4
% 2.89/1.43  
% 2.89/1.43  %Foreground sorts:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Background operators:
% 2.89/1.43  
% 2.89/1.43  
% 2.89/1.43  %Foreground operators:
% 2.89/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.43  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.89/1.43  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.89/1.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.89/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.43  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.89/1.43  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.89/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.89/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.43  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.89/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.43  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.89/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.89/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.89/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.43  
% 3.23/1.44  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.44  tff(f_117, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_1)).
% 3.23/1.44  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.23/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.44  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.23/1.44  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.23/1.44  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.23/1.44  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.23/1.44  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.23/1.44  tff(f_107, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.23/1.44  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.23/1.44  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.23/1.44  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.23/1.44  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.44  tff(c_74, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.23/1.44  tff(c_76, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.23/1.44  tff(c_22, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.44  tff(c_205, plain, (![A_68, B_69]: (k5_setfam_1(A_68, B_69)=k3_tarski(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.44  tff(c_210, plain, (![A_68]: (k5_setfam_1(A_68, k1_xboole_0)=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_205])).
% 3.23/1.44  tff(c_245, plain, (![A_79, B_80]: (m1_subset_1(k5_setfam_1(A_79, B_80), k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.44  tff(c_257, plain, (![A_68]: (m1_subset_1(k3_tarski(k1_xboole_0), k1_zfmisc_1(A_68)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(superposition, [status(thm), theory('equality')], [c_210, c_245])).
% 3.23/1.44  tff(c_263, plain, (![A_81]: (m1_subset_1(k3_tarski(k1_xboole_0), k1_zfmisc_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_257])).
% 3.23/1.44  tff(c_30, plain, (![A_20, C_22, B_21]: (m1_subset_1(A_20, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(C_22)) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.44  tff(c_291, plain, (![A_83, A_84]: (m1_subset_1(A_83, A_84) | ~r2_hidden(A_83, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_263, c_30])).
% 3.23/1.44  tff(c_302, plain, (![A_84]: (m1_subset_1('#skF_1'(k3_tarski(k1_xboole_0)), A_84) | v1_xboole_0(k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_291])).
% 3.23/1.44  tff(c_338, plain, (v1_xboole_0(k3_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_302])).
% 3.23/1.44  tff(c_83, plain, (![A_46]: (r2_hidden('#skF_2'(A_46), A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.44  tff(c_91, plain, (![A_46]: (~v1_xboole_0(A_46) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_83, c_2])).
% 3.23/1.44  tff(c_342, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_338, c_91])).
% 3.23/1.44  tff(c_26, plain, (![A_16, B_17]: (k5_setfam_1(A_16, B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.44  tff(c_275, plain, (![A_16]: (k5_setfam_1(A_16, k3_tarski(k1_xboole_0))=k3_tarski(k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_263, c_26])).
% 3.23/1.44  tff(c_345, plain, (![A_16]: (k5_setfam_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_342, c_275])).
% 3.23/1.44  tff(c_714, plain, (![A_148, B_149]: (r2_hidden(k5_setfam_1(u1_struct_0(A_148), B_149), u1_pre_topc(A_148)) | ~r1_tarski(B_149, u1_pre_topc(A_148)) | ~m1_subset_1(B_149, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148)))) | ~v2_pre_topc(A_148) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.23/1.44  tff(c_724, plain, (![A_148]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_148)) | ~r1_tarski(k1_xboole_0, u1_pre_topc(A_148)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148)))) | ~v2_pre_topc(A_148) | ~l1_pre_topc(A_148))), inference(superposition, [status(thm), theory('equality')], [c_345, c_714])).
% 3.23/1.44  tff(c_729, plain, (![A_150]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_150)) | ~v2_pre_topc(A_150) | ~l1_pre_topc(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8, c_724])).
% 3.23/1.44  tff(c_160, plain, (![A_61]: (k3_yellow_0(k2_yellow_1(A_61))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.44  tff(c_72, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_8')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.23/1.44  tff(c_171, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_8')) | v1_xboole_0(u1_pre_topc('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_72])).
% 3.23/1.44  tff(c_173, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_8'))), inference(splitLeft, [status(thm)], [c_171])).
% 3.23/1.44  tff(c_732, plain, (~v2_pre_topc('#skF_8') | ~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_729, c_173])).
% 3.23/1.44  tff(c_742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_732])).
% 3.23/1.44  tff(c_744, plain, (~v1_xboole_0(k3_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_302])).
% 3.23/1.44  tff(c_146, plain, (![A_59, B_60]: (r2_hidden(A_59, B_60) | v1_xboole_0(B_60) | ~m1_subset_1(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.23/1.44  tff(c_10, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.44  tff(c_157, plain, (![A_59, A_8]: (r1_tarski(A_59, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_59, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_146, c_10])).
% 3.23/1.44  tff(c_276, plain, (![A_82]: (r1_tarski(k3_tarski(k1_xboole_0), A_82) | v1_xboole_0(k1_zfmisc_1(A_82)))), inference(resolution, [status(thm)], [c_263, c_157])).
% 3.23/1.44  tff(c_92, plain, (![A_47]: (v1_xboole_0(A_47) | r2_hidden('#skF_1'(A_47), A_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.44  tff(c_32, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.44  tff(c_99, plain, (![A_47]: (~r1_tarski(A_47, '#skF_1'(A_47)) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_92, c_32])).
% 3.23/1.44  tff(c_290, plain, (v1_xboole_0(k3_tarski(k1_xboole_0)) | v1_xboole_0(k1_zfmisc_1('#skF_1'(k3_tarski(k1_xboole_0))))), inference(resolution, [status(thm)], [c_276, c_99])).
% 3.23/1.44  tff(c_760, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'(k3_tarski(k1_xboole_0))))), inference(negUnitSimplification, [status(thm)], [c_744, c_290])).
% 3.23/1.44  tff(c_120, plain, (![C_51, A_52]: (r2_hidden(C_51, k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.44  tff(c_128, plain, (![A_52, C_51]: (~v1_xboole_0(k1_zfmisc_1(A_52)) | ~r1_tarski(C_51, A_52))), inference(resolution, [status(thm)], [c_120, c_2])).
% 3.23/1.44  tff(c_768, plain, (![C_152]: (~r1_tarski(C_152, '#skF_1'(k3_tarski(k1_xboole_0))))), inference(resolution, [status(thm)], [c_760, c_128])).
% 3.23/1.44  tff(c_790, plain, $false, inference(resolution, [status(thm)], [c_8, c_768])).
% 3.23/1.44  tff(c_791, plain, (v1_xboole_0(u1_pre_topc('#skF_8'))), inference(splitRight, [status(thm)], [c_171])).
% 3.23/1.44  tff(c_805, plain, (u1_pre_topc('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_791, c_91])).
% 3.23/1.44  tff(c_792, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_8'))), inference(splitRight, [status(thm)], [c_171])).
% 3.23/1.44  tff(c_818, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_805, c_792])).
% 3.23/1.44  tff(c_821, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_818, c_32])).
% 3.23/1.44  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_821])).
% 3.23/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.44  
% 3.23/1.44  Inference rules
% 3.23/1.44  ----------------------
% 3.23/1.44  #Ref     : 0
% 3.23/1.44  #Sup     : 152
% 3.23/1.44  #Fact    : 0
% 3.23/1.44  #Define  : 0
% 3.23/1.44  #Split   : 3
% 3.23/1.44  #Chain   : 0
% 3.23/1.44  #Close   : 0
% 3.23/1.44  
% 3.23/1.45  Ordering : KBO
% 3.23/1.45  
% 3.23/1.45  Simplification rules
% 3.23/1.45  ----------------------
% 3.23/1.45  #Subsume      : 6
% 3.23/1.45  #Demod        : 80
% 3.23/1.45  #Tautology    : 52
% 3.23/1.45  #SimpNegUnit  : 1
% 3.23/1.45  #BackRed      : 9
% 3.23/1.45  
% 3.23/1.45  #Partial instantiations: 0
% 3.23/1.45  #Strategies tried      : 1
% 3.23/1.45  
% 3.23/1.45  Timing (in seconds)
% 3.23/1.45  ----------------------
% 3.23/1.45  Preprocessing        : 0.34
% 3.23/1.45  Parsing              : 0.17
% 3.23/1.45  CNF conversion       : 0.03
% 3.23/1.45  Main loop            : 0.36
% 3.23/1.45  Inferencing          : 0.13
% 3.23/1.45  Reduction            : 0.10
% 3.23/1.45  Demodulation         : 0.07
% 3.23/1.45  BG Simplification    : 0.02
% 3.23/1.45  Subsumption          : 0.08
% 3.23/1.45  Abstraction          : 0.02
% 3.23/1.45  MUC search           : 0.00
% 3.23/1.45  Cooper               : 0.00
% 3.23/1.45  Total                : 0.73
% 3.23/1.45  Index Insertion      : 0.00
% 3.23/1.45  Index Deletion       : 0.00
% 3.23/1.45  Index Matching       : 0.00
% 3.23/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
