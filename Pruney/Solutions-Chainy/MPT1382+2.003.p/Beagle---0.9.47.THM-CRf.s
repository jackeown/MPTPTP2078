%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 307 expanded)
%              Number of leaves         :   28 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 (1193 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_919,plain,(
    ! [B_170,A_171,C_172] :
      ( r2_hidden(B_170,k1_tops_1(A_171,C_172))
      | ~ m1_connsp_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(B_170,u1_struct_0(A_171))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_926,plain,(
    ! [B_170] :
      ( r2_hidden(B_170,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_919])).

tff(c_934,plain,(
    ! [B_170] :
      ( r2_hidden(B_170,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_926])).

tff(c_935,plain,(
    ! [B_170] :
      ( r2_hidden(B_170,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_170)
      | ~ m1_subset_1(B_170,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_934])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_936,plain,(
    ! [B_173] :
      ( r2_hidden(B_173,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_173)
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_934])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    ! [B_9,A_70,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_70,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_952,plain,(
    ! [B_9,B_173] :
      ( ~ v1_xboole_0(B_9)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_9)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_173)
      | ~ m1_subset_1(B_173,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_936,c_96])).

tff(c_955,plain,(
    ! [B_174] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_958,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_955])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_958])).

tff(c_965,plain,(
    ! [B_176] :
      ( ~ v1_xboole_0(B_176)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_176) ) ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_1004,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_965])).

tff(c_180,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_tops_1(A_94,B_95),B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_189,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_185])).

tff(c_204,plain,(
    ! [A_96,B_97] :
      ( v3_pre_topc(k1_tops_1(A_96,B_97),A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_209,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_204])).

tff(c_213,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_209])).

tff(c_49,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_88)
      | ~ r1_tarski(A_86,B_88)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_113,B_114,B_115,B_116] :
      ( r2_hidden('#skF_1'(A_113,B_114),B_115)
      | ~ r1_tarski(B_116,B_115)
      | ~ r1_tarski(A_113,B_116)
      | r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_311,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_1'(A_117,B_118),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_117,'#skF_4')
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_53,c_292])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_323,plain,(
    ! [A_119] :
      ( ~ r1_tarski(A_119,'#skF_4')
      | r1_tarski(A_119,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_149,plain,(
    ! [A_86,B_87,B_2,B_88] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_2)
      | ~ r1_tarski(B_88,B_2)
      | ~ r1_tarski(A_86,B_88)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_593,plain,(
    ! [A_147,B_148,A_149] :
      ( r2_hidden('#skF_1'(A_147,B_148),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_147,A_149)
      | r1_tarski(A_147,B_148)
      | ~ r1_tarski(A_149,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_323,c_149])).

tff(c_601,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_4'),B_148),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_148)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_189,c_593])).

tff(c_630,plain,(
    ! [B_152] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_4'),B_152),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_601])).

tff(c_641,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_630,c_4])).

tff(c_322,plain,(
    ! [A_117] :
      ( ~ r1_tarski(A_117,'#skF_4')
      | r1_tarski(A_117,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_26,plain,(
    ! [B_26,D_32,C_30,A_18] :
      ( k1_tops_1(B_26,D_32) = D_32
      | ~ v3_pre_topc(D_32,B_26)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_386,plain,(
    ! [C_123,A_124] :
      ( ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_393,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_386])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_393])).

tff(c_457,plain,(
    ! [B_129,D_130] :
      ( k1_tops_1(B_129,D_130) = D_130
      | ~ v3_pre_topc(D_130,B_129)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(B_129)))
      | ~ l1_pre_topc(B_129) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_469,plain,(
    ! [B_131,A_132] :
      ( k1_tops_1(B_131,A_132) = A_132
      | ~ v3_pre_topc(A_132,B_131)
      | ~ l1_pre_topc(B_131)
      | ~ r1_tarski(A_132,u1_struct_0(B_131)) ) ),
    inference(resolution,[status(thm)],[c_16,c_457])).

tff(c_472,plain,(
    ! [A_117] :
      ( k1_tops_1('#skF_2',A_117) = A_117
      | ~ v3_pre_topc(A_117,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_117,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_322,c_469])).

tff(c_502,plain,(
    ! [A_133] :
      ( k1_tops_1('#skF_2',A_133) = A_133
      | ~ v3_pre_topc(A_133,'#skF_2')
      | ~ r1_tarski(A_133,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_472])).

tff(c_509,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_213,c_502])).

tff(c_515,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_509])).

tff(c_720,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_connsp_2(C_159,A_160,B_161)
      | ~ r2_hidden(B_161,k1_tops_1(A_160,C_159))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_725,plain,(
    ! [B_161] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_161)
      | ~ r2_hidden(B_161,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_720])).

tff(c_734,plain,(
    ! [B_161] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_161)
      | ~ r2_hidden(B_161,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_725])).

tff(c_735,plain,(
    ! [B_161] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_161)
      | ~ r2_hidden(B_161,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_734])).

tff(c_818,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_821,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_818])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_821])).

tff(c_1005,plain,(
    ! [B_177] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_177)
      | ~ r2_hidden(B_177,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_62,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(A_60,k1_zfmisc_1(B_61))
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [D_55] :
      ( ~ r1_tarski(D_55,'#skF_4')
      | ~ v3_pre_topc(D_55,'#skF_2')
      | ~ m1_connsp_2(D_55,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_70,plain,(
    ! [A_60] :
      ( ~ r1_tarski(A_60,'#skF_4')
      | ~ v3_pre_topc(A_60,'#skF_2')
      | ~ m1_connsp_2(A_60,'#skF_2','#skF_3')
      | v1_xboole_0(A_60)
      | ~ r1_tarski(A_60,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_62,c_34])).

tff(c_339,plain,(
    ! [A_119] :
      ( ~ v3_pre_topc(A_119,'#skF_2')
      | ~ m1_connsp_2(A_119,'#skF_2','#skF_3')
      | v1_xboole_0(A_119)
      | ~ r1_tarski(A_119,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_323,c_70])).

tff(c_1012,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1005,c_339])).

tff(c_1018,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_189,c_213,c_1012])).

tff(c_1019,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_1018])).

tff(c_1026,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_935,c_1019])).

tff(c_1030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  
% 3.39/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.39/1.56  
% 3.39/1.56  %Foreground sorts:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Background operators:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Foreground operators:
% 3.39/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.39/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.39/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.39/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.56  
% 3.39/1.58  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.39/1.58  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.39/1.58  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.58  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.58  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.39/1.58  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.39/1.58  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.39/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.39/1.58  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.39/1.58  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_36, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_919, plain, (![B_170, A_171, C_172]: (r2_hidden(B_170, k1_tops_1(A_171, C_172)) | ~m1_connsp_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(B_170, u1_struct_0(A_171)) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.58  tff(c_926, plain, (![B_170]: (r2_hidden(B_170, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_170) | ~m1_subset_1(B_170, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_919])).
% 3.39/1.58  tff(c_934, plain, (![B_170]: (r2_hidden(B_170, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_170) | ~m1_subset_1(B_170, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_926])).
% 3.39/1.58  tff(c_935, plain, (![B_170]: (r2_hidden(B_170, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_170) | ~m1_subset_1(B_170, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_934])).
% 3.39/1.58  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.58  tff(c_936, plain, (![B_173]: (r2_hidden(B_173, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_173) | ~m1_subset_1(B_173, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_934])).
% 3.39/1.58  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.58  tff(c_91, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.58  tff(c_96, plain, (![B_9, A_70, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_70, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_91])).
% 3.39/1.58  tff(c_952, plain, (![B_9, B_173]: (~v1_xboole_0(B_9) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_9) | ~m1_connsp_2('#skF_4', '#skF_2', B_173) | ~m1_subset_1(B_173, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_936, c_96])).
% 3.39/1.58  tff(c_955, plain, (![B_174]: (~m1_connsp_2('#skF_4', '#skF_2', B_174) | ~m1_subset_1(B_174, u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_952])).
% 3.39/1.58  tff(c_958, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_955])).
% 3.39/1.58  tff(c_962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_958])).
% 3.39/1.58  tff(c_965, plain, (![B_176]: (~v1_xboole_0(B_176) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_176))), inference(splitRight, [status(thm)], [c_952])).
% 3.39/1.58  tff(c_1004, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_965])).
% 3.39/1.58  tff(c_180, plain, (![A_94, B_95]: (r1_tarski(k1_tops_1(A_94, B_95), B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.58  tff(c_185, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_180])).
% 3.39/1.58  tff(c_189, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_185])).
% 3.39/1.58  tff(c_204, plain, (![A_96, B_97]: (v3_pre_topc(k1_tops_1(A_96, B_97), A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.58  tff(c_209, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_204])).
% 3.39/1.58  tff(c_213, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_209])).
% 3.39/1.58  tff(c_49, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.58  tff(c_53, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 3.39/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.58  tff(c_135, plain, (![C_81, B_82, A_83]: (r2_hidden(C_81, B_82) | ~r2_hidden(C_81, A_83) | ~r1_tarski(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.58  tff(c_140, plain, (![A_86, B_87, B_88]: (r2_hidden('#skF_1'(A_86, B_87), B_88) | ~r1_tarski(A_86, B_88) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_6, c_135])).
% 3.39/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.58  tff(c_292, plain, (![A_113, B_114, B_115, B_116]: (r2_hidden('#skF_1'(A_113, B_114), B_115) | ~r1_tarski(B_116, B_115) | ~r1_tarski(A_113, B_116) | r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.39/1.58  tff(c_311, plain, (![A_117, B_118]: (r2_hidden('#skF_1'(A_117, B_118), u1_struct_0('#skF_2')) | ~r1_tarski(A_117, '#skF_4') | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_53, c_292])).
% 3.39/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.58  tff(c_323, plain, (![A_119]: (~r1_tarski(A_119, '#skF_4') | r1_tarski(A_119, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_311, c_4])).
% 3.39/1.58  tff(c_149, plain, (![A_86, B_87, B_2, B_88]: (r2_hidden('#skF_1'(A_86, B_87), B_2) | ~r1_tarski(B_88, B_2) | ~r1_tarski(A_86, B_88) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.39/1.58  tff(c_593, plain, (![A_147, B_148, A_149]: (r2_hidden('#skF_1'(A_147, B_148), u1_struct_0('#skF_2')) | ~r1_tarski(A_147, A_149) | r1_tarski(A_147, B_148) | ~r1_tarski(A_149, '#skF_4'))), inference(resolution, [status(thm)], [c_323, c_149])).
% 3.39/1.58  tff(c_601, plain, (![B_148]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_4'), B_148), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_148) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_189, c_593])).
% 3.39/1.58  tff(c_630, plain, (![B_152]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_4'), B_152), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_601])).
% 3.39/1.58  tff(c_641, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_630, c_4])).
% 3.39/1.58  tff(c_322, plain, (![A_117]: (~r1_tarski(A_117, '#skF_4') | r1_tarski(A_117, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_311, c_4])).
% 3.39/1.58  tff(c_26, plain, (![B_26, D_32, C_30, A_18]: (k1_tops_1(B_26, D_32)=D_32 | ~v3_pre_topc(D_32, B_26) | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_26))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.39/1.58  tff(c_386, plain, (![C_123, A_124]: (~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(splitLeft, [status(thm)], [c_26])).
% 3.39/1.58  tff(c_393, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_386])).
% 3.39/1.58  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_393])).
% 3.39/1.58  tff(c_457, plain, (![B_129, D_130]: (k1_tops_1(B_129, D_130)=D_130 | ~v3_pre_topc(D_130, B_129) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(B_129))) | ~l1_pre_topc(B_129))), inference(splitRight, [status(thm)], [c_26])).
% 3.39/1.58  tff(c_469, plain, (![B_131, A_132]: (k1_tops_1(B_131, A_132)=A_132 | ~v3_pre_topc(A_132, B_131) | ~l1_pre_topc(B_131) | ~r1_tarski(A_132, u1_struct_0(B_131)))), inference(resolution, [status(thm)], [c_16, c_457])).
% 3.39/1.58  tff(c_472, plain, (![A_117]: (k1_tops_1('#skF_2', A_117)=A_117 | ~v3_pre_topc(A_117, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_117, '#skF_4'))), inference(resolution, [status(thm)], [c_322, c_469])).
% 3.39/1.58  tff(c_502, plain, (![A_133]: (k1_tops_1('#skF_2', A_133)=A_133 | ~v3_pre_topc(A_133, '#skF_2') | ~r1_tarski(A_133, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_472])).
% 3.39/1.58  tff(c_509, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_213, c_502])).
% 3.39/1.58  tff(c_515, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_509])).
% 3.39/1.58  tff(c_720, plain, (![C_159, A_160, B_161]: (m1_connsp_2(C_159, A_160, B_161) | ~r2_hidden(B_161, k1_tops_1(A_160, C_159)) | ~m1_subset_1(C_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.58  tff(c_725, plain, (![B_161]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_161) | ~r2_hidden(B_161, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_161, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_720])).
% 3.39/1.58  tff(c_734, plain, (![B_161]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_161) | ~r2_hidden(B_161, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_161, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_725])).
% 3.39/1.58  tff(c_735, plain, (![B_161]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_161) | ~r2_hidden(B_161, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_161, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_734])).
% 3.39/1.58  tff(c_818, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_735])).
% 3.39/1.58  tff(c_821, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_818])).
% 3.39/1.58  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_821])).
% 3.39/1.58  tff(c_1005, plain, (![B_177]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_177) | ~r2_hidden(B_177, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_177, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_735])).
% 3.39/1.58  tff(c_62, plain, (![A_60, B_61]: (m1_subset_1(A_60, k1_zfmisc_1(B_61)) | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.58  tff(c_34, plain, (![D_55]: (~r1_tarski(D_55, '#skF_4') | ~v3_pre_topc(D_55, '#skF_2') | ~m1_connsp_2(D_55, '#skF_2', '#skF_3') | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_55))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.58  tff(c_70, plain, (![A_60]: (~r1_tarski(A_60, '#skF_4') | ~v3_pre_topc(A_60, '#skF_2') | ~m1_connsp_2(A_60, '#skF_2', '#skF_3') | v1_xboole_0(A_60) | ~r1_tarski(A_60, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_62, c_34])).
% 3.39/1.58  tff(c_339, plain, (![A_119]: (~v3_pre_topc(A_119, '#skF_2') | ~m1_connsp_2(A_119, '#skF_2', '#skF_3') | v1_xboole_0(A_119) | ~r1_tarski(A_119, '#skF_4'))), inference(resolution, [status(thm)], [c_323, c_70])).
% 3.39/1.58  tff(c_1012, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1005, c_339])).
% 3.39/1.58  tff(c_1018, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_189, c_213, c_1012])).
% 3.39/1.58  tff(c_1019, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1004, c_1018])).
% 3.39/1.58  tff(c_1026, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_935, c_1019])).
% 3.39/1.58  tff(c_1030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1026])).
% 3.39/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  
% 3.39/1.58  Inference rules
% 3.39/1.58  ----------------------
% 3.39/1.58  #Ref     : 0
% 3.39/1.58  #Sup     : 204
% 3.39/1.58  #Fact    : 0
% 3.39/1.58  #Define  : 0
% 3.39/1.58  #Split   : 13
% 3.39/1.58  #Chain   : 0
% 3.39/1.58  #Close   : 0
% 3.39/1.58  
% 3.39/1.58  Ordering : KBO
% 3.39/1.58  
% 3.39/1.58  Simplification rules
% 3.39/1.58  ----------------------
% 3.39/1.58  #Subsume      : 91
% 3.39/1.58  #Demod        : 105
% 3.39/1.58  #Tautology    : 28
% 3.39/1.58  #SimpNegUnit  : 11
% 3.39/1.58  #BackRed      : 0
% 3.39/1.58  
% 3.39/1.58  #Partial instantiations: 0
% 3.39/1.58  #Strategies tried      : 1
% 3.39/1.58  
% 3.39/1.58  Timing (in seconds)
% 3.39/1.58  ----------------------
% 3.39/1.58  Preprocessing        : 0.31
% 3.39/1.58  Parsing              : 0.17
% 3.39/1.58  CNF conversion       : 0.03
% 3.39/1.58  Main loop            : 0.43
% 3.39/1.58  Inferencing          : 0.15
% 3.39/1.58  Reduction            : 0.12
% 3.39/1.58  Demodulation         : 0.08
% 3.39/1.58  BG Simplification    : 0.02
% 3.39/1.58  Subsumption          : 0.11
% 3.39/1.58  Abstraction          : 0.02
% 3.39/1.58  MUC search           : 0.00
% 3.39/1.58  Cooper               : 0.00
% 3.39/1.58  Total                : 0.78
% 3.39/1.58  Index Insertion      : 0.00
% 3.39/1.58  Index Deletion       : 0.00
% 3.39/1.58  Index Matching       : 0.00
% 3.39/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
