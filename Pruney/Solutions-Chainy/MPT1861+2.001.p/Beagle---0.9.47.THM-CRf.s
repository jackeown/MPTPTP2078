%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 25.43s
% Output     : CNFRefutation 25.57s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 178 expanded)
%              Number of leaves         :   30 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 316 expanded)
%              Number of equality atoms :   28 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_166,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(B_49,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_124])).

tff(c_34,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [B_49,A_48] : k3_xboole_0(B_49,A_48) = k3_xboole_0(A_48,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_34])).

tff(c_189,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_34])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_228,plain,(
    ! [B_52,A_53] : r1_tarski(k3_xboole_0(B_52,A_53),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_26])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_959,plain,(
    ! [B_92,A_93] : k3_xboole_0(k3_xboole_0(B_92,A_93),A_93) = k3_xboole_0(B_92,A_93) ),
    inference(resolution,[status(thm)],[c_228,c_28])).

tff(c_1222,plain,(
    ! [B_97,A_98] : k3_xboole_0(k3_xboole_0(B_97,A_98),B_97) = k3_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_959])).

tff(c_1342,plain,(
    ! [A_48,A_98] : k3_xboole_0(A_48,k3_xboole_0(A_48,A_98)) = k3_xboole_0(A_98,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_1222])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,
    ( v2_tex_2('#skF_6','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_310,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2705,plain,(
    ! [A_150,B_151,B_152] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_150,B_151),B_152),A_150)
      | r1_tarski(k3_xboole_0(A_150,B_151),B_152) ) ),
    inference(resolution,[status(thm)],[c_310,c_12])).

tff(c_87,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_100,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,(
    k3_xboole_0('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_99,c_100])).

tff(c_278,plain,(
    ! [D_57,B_58,A_59] :
      ( r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k3_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_57,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_278])).

tff(c_299,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_308,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_62,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_296,c_299])).

tff(c_2787,plain,(
    ! [B_151] : r1_tarski(k3_xboole_0('#skF_5',B_151),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2705,c_308])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2235,plain,(
    ! [C_128,A_129,B_130] :
      ( v2_tex_2(C_128,A_129)
      | ~ v2_tex_2(B_130,A_129)
      | ~ r1_tarski(C_128,B_130)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9403,plain,(
    ! [A_242,B_243,A_244] :
      ( v2_tex_2(k3_xboole_0(A_242,B_243),A_244)
      | ~ v2_tex_2(A_242,A_244)
      | ~ m1_subset_1(k3_xboole_0(A_242,B_243),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_subset_1(A_242,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_26,c_2235])).

tff(c_44454,plain,(
    ! [A_602,B_603,A_604] :
      ( v2_tex_2(k3_xboole_0(A_602,B_603),A_604)
      | ~ v2_tex_2(A_602,A_604)
      | ~ m1_subset_1(A_602,k1_zfmisc_1(u1_struct_0(A_604)))
      | ~ l1_pre_topc(A_604)
      | ~ r1_tarski(k3_xboole_0(A_602,B_603),u1_struct_0(A_604)) ) ),
    inference(resolution,[status(thm)],[c_38,c_9403])).

tff(c_44609,plain,(
    ! [B_151] :
      ( v2_tex_2(k3_xboole_0('#skF_5',B_151),'#skF_4')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2787,c_44454])).

tff(c_44774,plain,(
    ! [B_605] : v2_tex_2(k3_xboole_0('#skF_5',B_605),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_52,c_44609])).

tff(c_44794,plain,(
    ! [A_98] : v2_tex_2(k3_xboole_0(A_98,'#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_44774])).

tff(c_642,plain,(
    ! [A_81,B_82,C_83] :
      ( k9_subset_1(A_81,B_82,C_83) = k3_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_650,plain,(
    ! [B_82] : k9_subset_1(u1_struct_0('#skF_4'),B_82,'#skF_6') = k3_xboole_0(B_82,'#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_642])).

tff(c_42,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_652,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_42])).

tff(c_653,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_652])).

tff(c_44832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44794,c_653])).

tff(c_44833,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_44886,plain,(
    ! [A_612,B_613] : k1_setfam_1(k2_tarski(A_612,B_613)) = k3_xboole_0(A_612,B_613) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44948,plain,(
    ! [A_616,B_617] : k1_setfam_1(k2_tarski(A_616,B_617)) = k3_xboole_0(B_617,A_616) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_44886])).

tff(c_44954,plain,(
    ! [B_617,A_616] : k3_xboole_0(B_617,A_616) = k3_xboole_0(A_616,B_617) ),
    inference(superposition,[status(thm),theory(equality)],[c_44948,c_34])).

tff(c_44868,plain,(
    ! [A_608,B_609] :
      ( k3_xboole_0(A_608,B_609) = A_608
      | ~ r1_tarski(A_608,B_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45140,plain,(
    ! [A_636,B_637] : k3_xboole_0(k3_xboole_0(A_636,B_637),A_636) = k3_xboole_0(A_636,B_637) ),
    inference(resolution,[status(thm)],[c_26,c_44868])).

tff(c_45183,plain,(
    ! [A_616,B_617] : k3_xboole_0(k3_xboole_0(A_616,B_617),B_617) = k3_xboole_0(B_617,A_616) ),
    inference(superposition,[status(thm),theory(equality)],[c_44954,c_45140])).

tff(c_45073,plain,(
    ! [A_629,B_630] :
      ( r2_hidden('#skF_1'(A_629,B_630),A_629)
      | r1_tarski(A_629,B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47500,plain,(
    ! [A_720,B_721,B_722] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_720,B_721),B_722),B_721)
      | r1_tarski(k3_xboole_0(A_720,B_721),B_722) ) ),
    inference(resolution,[status(thm)],[c_45073,c_10])).

tff(c_44873,plain,(
    ! [A_610,B_611] :
      ( r1_tarski(A_610,B_611)
      | ~ m1_subset_1(A_610,k1_zfmisc_1(B_611)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44880,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_44873])).

tff(c_44885,plain,(
    k3_xboole_0('#skF_6',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44880,c_28])).

tff(c_44971,plain,(
    ! [D_618,B_619,A_620] :
      ( r2_hidden(D_618,B_619)
      | ~ r2_hidden(D_618,k3_xboole_0(A_620,B_619)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44983,plain,(
    ! [D_618] :
      ( r2_hidden(D_618,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_618,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44885,c_44971])).

tff(c_45062,plain,(
    ! [A_627,B_628] :
      ( ~ r2_hidden('#skF_1'(A_627,B_628),B_628)
      | r1_tarski(A_627,B_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45072,plain,(
    ! [A_627] :
      ( r1_tarski(A_627,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_627,u1_struct_0('#skF_4')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44983,c_45062])).

tff(c_47604,plain,(
    ! [A_723] : r1_tarski(k3_xboole_0(A_723,'#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_47500,c_45072])).

tff(c_47625,plain,(
    ! [A_616] : r1_tarski(k3_xboole_0('#skF_6',A_616),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45183,c_47604])).

tff(c_46940,plain,(
    ! [C_695,A_696,B_697] :
      ( v2_tex_2(C_695,A_696)
      | ~ v2_tex_2(B_697,A_696)
      | ~ r1_tarski(C_695,B_697)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(u1_struct_0(A_696)))
      | ~ m1_subset_1(B_697,k1_zfmisc_1(u1_struct_0(A_696)))
      | ~ l1_pre_topc(A_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55493,plain,(
    ! [A_830,B_831,A_832] :
      ( v2_tex_2(k3_xboole_0(A_830,B_831),A_832)
      | ~ v2_tex_2(A_830,A_832)
      | ~ m1_subset_1(k3_xboole_0(A_830,B_831),k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ m1_subset_1(A_830,k1_zfmisc_1(u1_struct_0(A_832)))
      | ~ l1_pre_topc(A_832) ) ),
    inference(resolution,[status(thm)],[c_26,c_46940])).

tff(c_95617,plain,(
    ! [A_1257,B_1258,A_1259] :
      ( v2_tex_2(k3_xboole_0(A_1257,B_1258),A_1259)
      | ~ v2_tex_2(A_1257,A_1259)
      | ~ m1_subset_1(A_1257,k1_zfmisc_1(u1_struct_0(A_1259)))
      | ~ l1_pre_topc(A_1259)
      | ~ r1_tarski(k3_xboole_0(A_1257,B_1258),u1_struct_0(A_1259)) ) ),
    inference(resolution,[status(thm)],[c_38,c_55493])).

tff(c_95784,plain,(
    ! [A_616] :
      ( v2_tex_2(k3_xboole_0('#skF_6',A_616),'#skF_4')
      | ~ v2_tex_2('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47625,c_95617])).

tff(c_95927,plain,(
    ! [A_616] : v2_tex_2(k3_xboole_0('#skF_6',A_616),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44833,c_95784])).

tff(c_45653,plain,(
    ! [A_652,B_653,C_654] :
      ( k9_subset_1(A_652,B_653,C_654) = k3_xboole_0(B_653,C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(A_652)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45661,plain,(
    ! [B_653] : k9_subset_1(u1_struct_0('#skF_4'),B_653,'#skF_6') = k3_xboole_0(B_653,'#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_45653])).

tff(c_45663,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45661,c_42])).

tff(c_45664,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44954,c_45663])).

tff(c_95957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95927,c_45664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.43/16.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.43/16.06  
% 25.43/16.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.54/16.07  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 25.54/16.07  
% 25.54/16.07  %Foreground sorts:
% 25.54/16.07  
% 25.54/16.07  
% 25.54/16.07  %Background operators:
% 25.54/16.07  
% 25.54/16.07  
% 25.54/16.07  %Foreground operators:
% 25.54/16.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.54/16.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.54/16.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 25.54/16.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.54/16.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.54/16.07  tff('#skF_5', type, '#skF_5': $i).
% 25.54/16.07  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 25.54/16.07  tff('#skF_6', type, '#skF_6': $i).
% 25.54/16.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.54/16.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.54/16.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.54/16.07  tff('#skF_4', type, '#skF_4': $i).
% 25.54/16.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 25.54/16.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.54/16.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.54/16.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.54/16.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 25.54/16.07  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 25.54/16.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.54/16.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 25.54/16.07  
% 25.57/16.09  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 25.57/16.09  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 25.57/16.09  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 25.57/16.09  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 25.57/16.09  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 25.57/16.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 25.57/16.09  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 25.57/16.09  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 25.57/16.09  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 25.57/16.09  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 25.57/16.09  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.57/16.09  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.57/16.09  tff(c_30, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.57/16.09  tff(c_124, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.57/16.09  tff(c_166, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(B_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_30, c_124])).
% 25.57/16.09  tff(c_34, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.57/16.09  tff(c_172, plain, (![B_49, A_48]: (k3_xboole_0(B_49, A_48)=k3_xboole_0(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_166, c_34])).
% 25.57/16.09  tff(c_189, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_166, c_34])).
% 25.57/16.09  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 25.57/16.09  tff(c_228, plain, (![B_52, A_53]: (r1_tarski(k3_xboole_0(B_52, A_53), A_53))), inference(superposition, [status(thm), theory('equality')], [c_189, c_26])).
% 25.57/16.09  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.57/16.09  tff(c_959, plain, (![B_92, A_93]: (k3_xboole_0(k3_xboole_0(B_92, A_93), A_93)=k3_xboole_0(B_92, A_93))), inference(resolution, [status(thm)], [c_228, c_28])).
% 25.57/16.09  tff(c_1222, plain, (![B_97, A_98]: (k3_xboole_0(k3_xboole_0(B_97, A_98), B_97)=k3_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_172, c_959])).
% 25.57/16.09  tff(c_1342, plain, (![A_48, A_98]: (k3_xboole_0(A_48, k3_xboole_0(A_48, A_98))=k3_xboole_0(A_98, A_48))), inference(superposition, [status(thm), theory('equality')], [c_172, c_1222])).
% 25.57/16.09  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.57/16.09  tff(c_44, plain, (v2_tex_2('#skF_6', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.57/16.09  tff(c_52, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 25.57/16.09  tff(c_310, plain, (![A_64, B_65]: (r2_hidden('#skF_1'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.57/16.09  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.57/16.09  tff(c_2705, plain, (![A_150, B_151, B_152]: (r2_hidden('#skF_1'(k3_xboole_0(A_150, B_151), B_152), A_150) | r1_tarski(k3_xboole_0(A_150, B_151), B_152))), inference(resolution, [status(thm)], [c_310, c_12])).
% 25.57/16.09  tff(c_87, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.57/16.09  tff(c_99, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_87])).
% 25.57/16.09  tff(c_100, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.57/16.09  tff(c_110, plain, (k3_xboole_0('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_99, c_100])).
% 25.57/16.09  tff(c_278, plain, (![D_57, B_58, A_59]: (r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k3_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.57/16.09  tff(c_296, plain, (![D_57]: (r2_hidden(D_57, u1_struct_0('#skF_4')) | ~r2_hidden(D_57, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_278])).
% 25.57/16.09  tff(c_299, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.57/16.09  tff(c_308, plain, (![A_62]: (r1_tarski(A_62, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_62, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_296, c_299])).
% 25.57/16.09  tff(c_2787, plain, (![B_151]: (r1_tarski(k3_xboole_0('#skF_5', B_151), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2705, c_308])).
% 25.57/16.09  tff(c_38, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.57/16.09  tff(c_2235, plain, (![C_128, A_129, B_130]: (v2_tex_2(C_128, A_129) | ~v2_tex_2(B_130, A_129) | ~r1_tarski(C_128, B_130) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.57/16.09  tff(c_9403, plain, (![A_242, B_243, A_244]: (v2_tex_2(k3_xboole_0(A_242, B_243), A_244) | ~v2_tex_2(A_242, A_244) | ~m1_subset_1(k3_xboole_0(A_242, B_243), k1_zfmisc_1(u1_struct_0(A_244))) | ~m1_subset_1(A_242, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_26, c_2235])).
% 25.57/16.09  tff(c_44454, plain, (![A_602, B_603, A_604]: (v2_tex_2(k3_xboole_0(A_602, B_603), A_604) | ~v2_tex_2(A_602, A_604) | ~m1_subset_1(A_602, k1_zfmisc_1(u1_struct_0(A_604))) | ~l1_pre_topc(A_604) | ~r1_tarski(k3_xboole_0(A_602, B_603), u1_struct_0(A_604)))), inference(resolution, [status(thm)], [c_38, c_9403])).
% 25.57/16.09  tff(c_44609, plain, (![B_151]: (v2_tex_2(k3_xboole_0('#skF_5', B_151), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_2787, c_44454])).
% 25.57/16.09  tff(c_44774, plain, (![B_605]: (v2_tex_2(k3_xboole_0('#skF_5', B_605), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_52, c_44609])).
% 25.57/16.09  tff(c_44794, plain, (![A_98]: (v2_tex_2(k3_xboole_0(A_98, '#skF_5'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1342, c_44774])).
% 25.57/16.09  tff(c_642, plain, (![A_81, B_82, C_83]: (k9_subset_1(A_81, B_82, C_83)=k3_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.57/16.09  tff(c_650, plain, (![B_82]: (k9_subset_1(u1_struct_0('#skF_4'), B_82, '#skF_6')=k3_xboole_0(B_82, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_642])).
% 25.57/16.09  tff(c_42, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 25.57/16.09  tff(c_652, plain, (~v2_tex_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_650, c_42])).
% 25.57/16.09  tff(c_653, plain, (~v2_tex_2(k3_xboole_0('#skF_6', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_652])).
% 25.57/16.09  tff(c_44832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44794, c_653])).
% 25.57/16.09  tff(c_44833, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 25.57/16.09  tff(c_44886, plain, (![A_612, B_613]: (k1_setfam_1(k2_tarski(A_612, B_613))=k3_xboole_0(A_612, B_613))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.57/16.09  tff(c_44948, plain, (![A_616, B_617]: (k1_setfam_1(k2_tarski(A_616, B_617))=k3_xboole_0(B_617, A_616))), inference(superposition, [status(thm), theory('equality')], [c_30, c_44886])).
% 25.57/16.09  tff(c_44954, plain, (![B_617, A_616]: (k3_xboole_0(B_617, A_616)=k3_xboole_0(A_616, B_617))), inference(superposition, [status(thm), theory('equality')], [c_44948, c_34])).
% 25.57/16.09  tff(c_44868, plain, (![A_608, B_609]: (k3_xboole_0(A_608, B_609)=A_608 | ~r1_tarski(A_608, B_609))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.57/16.09  tff(c_45140, plain, (![A_636, B_637]: (k3_xboole_0(k3_xboole_0(A_636, B_637), A_636)=k3_xboole_0(A_636, B_637))), inference(resolution, [status(thm)], [c_26, c_44868])).
% 25.57/16.09  tff(c_45183, plain, (![A_616, B_617]: (k3_xboole_0(k3_xboole_0(A_616, B_617), B_617)=k3_xboole_0(B_617, A_616))), inference(superposition, [status(thm), theory('equality')], [c_44954, c_45140])).
% 25.57/16.09  tff(c_45073, plain, (![A_629, B_630]: (r2_hidden('#skF_1'(A_629, B_630), A_629) | r1_tarski(A_629, B_630))), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.57/16.09  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.57/16.09  tff(c_47500, plain, (![A_720, B_721, B_722]: (r2_hidden('#skF_1'(k3_xboole_0(A_720, B_721), B_722), B_721) | r1_tarski(k3_xboole_0(A_720, B_721), B_722))), inference(resolution, [status(thm)], [c_45073, c_10])).
% 25.57/16.09  tff(c_44873, plain, (![A_610, B_611]: (r1_tarski(A_610, B_611) | ~m1_subset_1(A_610, k1_zfmisc_1(B_611)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.57/16.09  tff(c_44880, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_44873])).
% 25.57/16.09  tff(c_44885, plain, (k3_xboole_0('#skF_6', u1_struct_0('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_44880, c_28])).
% 25.57/16.09  tff(c_44971, plain, (![D_618, B_619, A_620]: (r2_hidden(D_618, B_619) | ~r2_hidden(D_618, k3_xboole_0(A_620, B_619)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.57/16.09  tff(c_44983, plain, (![D_618]: (r2_hidden(D_618, u1_struct_0('#skF_4')) | ~r2_hidden(D_618, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44885, c_44971])).
% 25.57/16.09  tff(c_45062, plain, (![A_627, B_628]: (~r2_hidden('#skF_1'(A_627, B_628), B_628) | r1_tarski(A_627, B_628))), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.57/16.09  tff(c_45072, plain, (![A_627]: (r1_tarski(A_627, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_627, u1_struct_0('#skF_4')), '#skF_6'))), inference(resolution, [status(thm)], [c_44983, c_45062])).
% 25.57/16.09  tff(c_47604, plain, (![A_723]: (r1_tarski(k3_xboole_0(A_723, '#skF_6'), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_47500, c_45072])).
% 25.57/16.09  tff(c_47625, plain, (![A_616]: (r1_tarski(k3_xboole_0('#skF_6', A_616), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_45183, c_47604])).
% 25.57/16.09  tff(c_46940, plain, (![C_695, A_696, B_697]: (v2_tex_2(C_695, A_696) | ~v2_tex_2(B_697, A_696) | ~r1_tarski(C_695, B_697) | ~m1_subset_1(C_695, k1_zfmisc_1(u1_struct_0(A_696))) | ~m1_subset_1(B_697, k1_zfmisc_1(u1_struct_0(A_696))) | ~l1_pre_topc(A_696))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.57/16.09  tff(c_55493, plain, (![A_830, B_831, A_832]: (v2_tex_2(k3_xboole_0(A_830, B_831), A_832) | ~v2_tex_2(A_830, A_832) | ~m1_subset_1(k3_xboole_0(A_830, B_831), k1_zfmisc_1(u1_struct_0(A_832))) | ~m1_subset_1(A_830, k1_zfmisc_1(u1_struct_0(A_832))) | ~l1_pre_topc(A_832))), inference(resolution, [status(thm)], [c_26, c_46940])).
% 25.57/16.09  tff(c_95617, plain, (![A_1257, B_1258, A_1259]: (v2_tex_2(k3_xboole_0(A_1257, B_1258), A_1259) | ~v2_tex_2(A_1257, A_1259) | ~m1_subset_1(A_1257, k1_zfmisc_1(u1_struct_0(A_1259))) | ~l1_pre_topc(A_1259) | ~r1_tarski(k3_xboole_0(A_1257, B_1258), u1_struct_0(A_1259)))), inference(resolution, [status(thm)], [c_38, c_55493])).
% 25.57/16.09  tff(c_95784, plain, (![A_616]: (v2_tex_2(k3_xboole_0('#skF_6', A_616), '#skF_4') | ~v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_47625, c_95617])).
% 25.57/16.09  tff(c_95927, plain, (![A_616]: (v2_tex_2(k3_xboole_0('#skF_6', A_616), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44833, c_95784])).
% 25.57/16.09  tff(c_45653, plain, (![A_652, B_653, C_654]: (k9_subset_1(A_652, B_653, C_654)=k3_xboole_0(B_653, C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(A_652)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.57/16.09  tff(c_45661, plain, (![B_653]: (k9_subset_1(u1_struct_0('#skF_4'), B_653, '#skF_6')=k3_xboole_0(B_653, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_45653])).
% 25.57/16.09  tff(c_45663, plain, (~v2_tex_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45661, c_42])).
% 25.57/16.09  tff(c_45664, plain, (~v2_tex_2(k3_xboole_0('#skF_6', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44954, c_45663])).
% 25.57/16.09  tff(c_95957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95927, c_45664])).
% 25.57/16.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.57/16.09  
% 25.57/16.09  Inference rules
% 25.57/16.09  ----------------------
% 25.57/16.09  #Ref     : 0
% 25.57/16.09  #Sup     : 24157
% 25.57/16.09  #Fact    : 0
% 25.57/16.09  #Define  : 0
% 25.57/16.09  #Split   : 2
% 25.57/16.09  #Chain   : 0
% 25.57/16.09  #Close   : 0
% 25.57/16.09  
% 25.57/16.09  Ordering : KBO
% 25.57/16.09  
% 25.57/16.09  Simplification rules
% 25.57/16.09  ----------------------
% 25.57/16.09  #Subsume      : 4495
% 25.57/16.09  #Demod        : 26939
% 25.57/16.09  #Tautology    : 9787
% 25.57/16.09  #SimpNegUnit  : 3
% 25.57/16.09  #BackRed      : 4
% 25.57/16.09  
% 25.57/16.09  #Partial instantiations: 0
% 25.57/16.09  #Strategies tried      : 1
% 25.57/16.09  
% 25.57/16.09  Timing (in seconds)
% 25.57/16.09  ----------------------
% 25.57/16.09  Preprocessing        : 0.32
% 25.57/16.09  Parsing              : 0.17
% 25.57/16.09  CNF conversion       : 0.02
% 25.57/16.09  Main loop            : 14.99
% 25.57/16.09  Inferencing          : 1.87
% 25.57/16.09  Reduction            : 8.47
% 25.57/16.09  Demodulation         : 7.72
% 25.57/16.09  BG Simplification    : 0.25
% 25.57/16.09  Subsumption          : 3.83
% 25.57/16.09  Abstraction          : 0.39
% 25.57/16.09  MUC search           : 0.00
% 25.57/16.09  Cooper               : 0.00
% 25.57/16.09  Total                : 15.35
% 25.57/16.09  Index Insertion      : 0.00
% 25.57/16.09  Index Deletion       : 0.00
% 25.57/16.09  Index Matching       : 0.00
% 25.57/16.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
