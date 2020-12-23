%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 37.20s
% Output     : CNFRefutation 37.24s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 180 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 383 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

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

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_193,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_79,B_80] :
      ( ~ v1_xboole_0(A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_30,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_129,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_86,c_129])).

tff(c_221,plain,(
    ! [A_81] :
      ( k1_xboole_0 = A_81
      | ~ v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_208,c_137])).

tff(c_225,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_221])).

tff(c_230,plain,(
    ! [A_18] : r1_tarski('#skF_6',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_86])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_561,plain,(
    ! [A_117,B_118] :
      ( r1_tarski('#skF_4'(A_117,B_118),B_118)
      | v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2155,plain,(
    ! [A_202,A_203] :
      ( r1_tarski('#skF_4'(A_202,A_203),A_203)
      | v2_tex_2(A_203,A_202)
      | ~ l1_pre_topc(A_202)
      | ~ r1_tarski(A_203,u1_struct_0(A_202)) ) ),
    inference(resolution,[status(thm)],[c_34,c_561])).

tff(c_229,plain,(
    ! [A_18] :
      ( A_18 = '#skF_6'
      | ~ r1_tarski(A_18,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_225,c_137])).

tff(c_2177,plain,(
    ! [A_202] :
      ( '#skF_4'(A_202,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_202)
      | ~ l1_pre_topc(A_202)
      | ~ r1_tarski('#skF_6',u1_struct_0(A_202)) ) ),
    inference(resolution,[status(thm)],[c_2155,c_229])).

tff(c_2192,plain,(
    ! [A_204] :
      ( '#skF_4'(A_204,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2177])).

tff(c_52,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2195,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2192,c_52])).

tff(c_2198,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2195])).

tff(c_207,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(A_77)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_492,plain,(
    ! [B_109,A_110] :
      ( v3_pre_topc(B_109,A_110)
      | ~ v1_xboole_0(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1704,plain,(
    ! [A_188,A_189] :
      ( v3_pre_topc(A_188,A_189)
      | ~ v1_xboole_0(A_188)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | ~ r1_tarski(A_188,u1_struct_0(A_189)) ) ),
    inference(resolution,[status(thm)],[c_34,c_492])).

tff(c_1744,plain,(
    ! [A_77,A_189] :
      ( v3_pre_topc(A_77,A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_207,c_1704])).

tff(c_231,plain,(
    ! [A_18] : m1_subset_1('#skF_6',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_30])).

tff(c_26,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [B_68,A_69] :
      ( m1_subset_1(B_68,A_69)
      | ~ r2_hidden(B_68,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_361,plain,(
    ! [A_95,B_96,C_97] :
      ( k9_subset_1(A_95,B_96,B_96) = B_96
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_366,plain,(
    ! [A_95,B_96] :
      ( k9_subset_1(A_95,B_96,B_96) = B_96
      | v1_xboole_0(k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_116,c_361])).

tff(c_375,plain,(
    ! [A_95,B_96] : k9_subset_1(A_95,B_96,B_96) = B_96 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_366])).

tff(c_870,plain,(
    ! [A_141,B_142,D_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,D_143) != '#skF_4'(A_141,B_142)
      | ~ v3_pre_topc(D_143,A_141)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_174231,plain,(
    ! [A_1312,B_1313] :
      ( '#skF_4'(A_1312,B_1313) != B_1313
      | ~ v3_pre_topc(B_1313,A_1312)
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1312)))
      | v2_tex_2(B_1313,A_1312)
      | ~ m1_subset_1(B_1313,k1_zfmisc_1(u1_struct_0(A_1312)))
      | ~ l1_pre_topc(A_1312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_870])).

tff(c_174340,plain,(
    ! [A_1312] :
      ( '#skF_4'(A_1312,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1312)
      | v2_tex_2('#skF_6',A_1312)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1312)))
      | ~ l1_pre_topc(A_1312) ) ),
    inference(resolution,[status(thm)],[c_231,c_174231])).

tff(c_174398,plain,(
    ! [A_1314] :
      ( '#skF_4'(A_1314,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1314)
      | v2_tex_2('#skF_6',A_1314)
      | ~ l1_pre_topc(A_1314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_174340])).

tff(c_174402,plain,(
    ! [A_189] :
      ( '#skF_4'(A_189,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1744,c_174398])).

tff(c_174410,plain,(
    ! [A_1315] :
      ( '#skF_4'(A_1315,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_1315)
      | ~ l1_pre_topc(A_1315)
      | ~ v2_pre_topc(A_1315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_174402])).

tff(c_174413,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_174410,c_52])).

tff(c_174417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2198,c_174413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.20/26.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.24/26.89  
% 37.24/26.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.24/26.89  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 37.24/26.89  
% 37.24/26.89  %Foreground sorts:
% 37.24/26.89  
% 37.24/26.89  
% 37.24/26.89  %Background operators:
% 37.24/26.89  
% 37.24/26.89  
% 37.24/26.89  %Foreground operators:
% 37.24/26.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 37.24/26.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 37.24/26.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.24/26.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.24/26.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 37.24/26.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.24/26.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 37.24/26.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.24/26.89  tff('#skF_5', type, '#skF_5': $i).
% 37.24/26.89  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 37.24/26.89  tff('#skF_6', type, '#skF_6': $i).
% 37.24/26.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.24/26.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.24/26.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 37.24/26.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.24/26.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.24/26.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 37.24/26.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 37.24/26.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.24/26.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 37.24/26.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 37.24/26.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.24/26.89  
% 37.24/26.91  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 37.24/26.91  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 37.24/26.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 37.24/26.91  tff(f_66, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 37.24/26.91  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 37.24/26.91  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 37.24/26.91  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 37.24/26.91  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 37.24/26.91  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 37.24/26.91  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 37.24/26.91  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 37.24/26.91  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 37.24/26.91  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 37.24/26.91  tff(c_56, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 37.24/26.91  tff(c_193, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), A_77) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.24/26.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.24/26.91  tff(c_208, plain, (![A_79, B_80]: (~v1_xboole_0(A_79) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_193, c_2])).
% 37.24/26.91  tff(c_30, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 37.24/26.91  tff(c_74, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 37.24/26.91  tff(c_86, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_30, c_74])).
% 37.24/26.91  tff(c_129, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.24/26.91  tff(c_137, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_86, c_129])).
% 37.24/26.91  tff(c_221, plain, (![A_81]: (k1_xboole_0=A_81 | ~v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_208, c_137])).
% 37.24/26.91  tff(c_225, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_56, c_221])).
% 37.24/26.91  tff(c_230, plain, (![A_18]: (r1_tarski('#skF_6', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_86])).
% 37.24/26.91  tff(c_34, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 37.24/26.91  tff(c_561, plain, (![A_117, B_118]: (r1_tarski('#skF_4'(A_117, B_118), B_118) | v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.24/26.91  tff(c_2155, plain, (![A_202, A_203]: (r1_tarski('#skF_4'(A_202, A_203), A_203) | v2_tex_2(A_203, A_202) | ~l1_pre_topc(A_202) | ~r1_tarski(A_203, u1_struct_0(A_202)))), inference(resolution, [status(thm)], [c_34, c_561])).
% 37.24/26.91  tff(c_229, plain, (![A_18]: (A_18='#skF_6' | ~r1_tarski(A_18, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_225, c_137])).
% 37.24/26.91  tff(c_2177, plain, (![A_202]: ('#skF_4'(A_202, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_202) | ~l1_pre_topc(A_202) | ~r1_tarski('#skF_6', u1_struct_0(A_202)))), inference(resolution, [status(thm)], [c_2155, c_229])).
% 37.24/26.91  tff(c_2192, plain, (![A_204]: ('#skF_4'(A_204, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_204) | ~l1_pre_topc(A_204))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_2177])).
% 37.24/26.91  tff(c_52, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 37.24/26.91  tff(c_2195, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2192, c_52])).
% 37.24/26.91  tff(c_2198, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2195])).
% 37.24/26.91  tff(c_207, plain, (![A_77, B_78]: (~v1_xboole_0(A_77) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_193, c_2])).
% 37.24/26.91  tff(c_492, plain, (![B_109, A_110]: (v3_pre_topc(B_109, A_110) | ~v1_xboole_0(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_87])).
% 37.24/26.91  tff(c_1704, plain, (![A_188, A_189]: (v3_pre_topc(A_188, A_189) | ~v1_xboole_0(A_188) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | ~r1_tarski(A_188, u1_struct_0(A_189)))), inference(resolution, [status(thm)], [c_34, c_492])).
% 37.24/26.91  tff(c_1744, plain, (![A_77, A_189]: (v3_pre_topc(A_77, A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_207, c_1704])).
% 37.24/26.91  tff(c_231, plain, (![A_18]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_30])).
% 37.24/26.91  tff(c_26, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 37.24/26.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 37.24/26.91  tff(c_112, plain, (![B_68, A_69]: (m1_subset_1(B_68, A_69) | ~r2_hidden(B_68, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 37.24/26.91  tff(c_116, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_112])).
% 37.24/26.91  tff(c_361, plain, (![A_95, B_96, C_97]: (k9_subset_1(A_95, B_96, B_96)=B_96 | ~m1_subset_1(C_97, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 37.24/26.91  tff(c_366, plain, (![A_95, B_96]: (k9_subset_1(A_95, B_96, B_96)=B_96 | v1_xboole_0(k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_116, c_361])).
% 37.24/26.91  tff(c_375, plain, (![A_95, B_96]: (k9_subset_1(A_95, B_96, B_96)=B_96)), inference(negUnitSimplification, [status(thm)], [c_26, c_366])).
% 37.24/26.91  tff(c_870, plain, (![A_141, B_142, D_143]: (k9_subset_1(u1_struct_0(A_141), B_142, D_143)!='#skF_4'(A_141, B_142) | ~v3_pre_topc(D_143, A_141) | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0(A_141))) | v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.24/26.91  tff(c_174231, plain, (![A_1312, B_1313]: ('#skF_4'(A_1312, B_1313)!=B_1313 | ~v3_pre_topc(B_1313, A_1312) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1312))) | v2_tex_2(B_1313, A_1312) | ~m1_subset_1(B_1313, k1_zfmisc_1(u1_struct_0(A_1312))) | ~l1_pre_topc(A_1312))), inference(superposition, [status(thm), theory('equality')], [c_375, c_870])).
% 37.24/26.91  tff(c_174340, plain, (![A_1312]: ('#skF_4'(A_1312, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1312) | v2_tex_2('#skF_6', A_1312) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1312))) | ~l1_pre_topc(A_1312))), inference(resolution, [status(thm)], [c_231, c_174231])).
% 37.24/26.91  tff(c_174398, plain, (![A_1314]: ('#skF_4'(A_1314, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1314) | v2_tex_2('#skF_6', A_1314) | ~l1_pre_topc(A_1314))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_174340])).
% 37.24/26.91  tff(c_174402, plain, (![A_189]: ('#skF_4'(A_189, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_1744, c_174398])).
% 37.24/26.91  tff(c_174410, plain, (![A_1315]: ('#skF_4'(A_1315, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_1315) | ~l1_pre_topc(A_1315) | ~v2_pre_topc(A_1315))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_174402])).
% 37.24/26.91  tff(c_174413, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_174410, c_52])).
% 37.24/26.91  tff(c_174417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2198, c_174413])).
% 37.24/26.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.24/26.91  
% 37.24/26.91  Inference rules
% 37.24/26.91  ----------------------
% 37.24/26.91  #Ref     : 0
% 37.24/26.91  #Sup     : 44993
% 37.24/26.91  #Fact    : 0
% 37.24/26.91  #Define  : 0
% 37.24/26.91  #Split   : 28
% 37.24/26.91  #Chain   : 0
% 37.24/26.91  #Close   : 0
% 37.24/26.91  
% 37.24/26.91  Ordering : KBO
% 37.24/26.91  
% 37.24/26.91  Simplification rules
% 37.24/26.91  ----------------------
% 37.24/26.91  #Subsume      : 23938
% 37.24/26.91  #Demod        : 26761
% 37.24/26.91  #Tautology    : 10638
% 37.24/26.91  #SimpNegUnit  : 4490
% 37.24/26.91  #BackRed      : 1022
% 37.24/26.91  
% 37.24/26.91  #Partial instantiations: 0
% 37.24/26.91  #Strategies tried      : 1
% 37.24/26.91  
% 37.24/26.91  Timing (in seconds)
% 37.24/26.91  ----------------------
% 37.24/26.91  Preprocessing        : 0.32
% 37.24/26.91  Parsing              : 0.18
% 37.24/26.91  CNF conversion       : 0.03
% 37.24/26.91  Main loop            : 25.88
% 37.24/26.91  Inferencing          : 3.00
% 37.24/26.91  Reduction            : 5.23
% 37.24/26.91  Demodulation         : 3.23
% 37.24/26.91  BG Simplification    : 0.35
% 37.24/26.91  Subsumption          : 16.08
% 37.24/26.91  Abstraction          : 0.62
% 37.24/26.91  MUC search           : 0.00
% 37.24/26.91  Cooper               : 0.00
% 37.24/26.91  Total                : 26.24
% 37.24/26.91  Index Insertion      : 0.00
% 37.24/26.91  Index Deletion       : 0.00
% 37.24/26.91  Index Matching       : 0.00
% 37.24/26.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
