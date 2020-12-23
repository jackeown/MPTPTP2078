%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 173 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 ( 650 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_151,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_43,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_541,plain,(
    ! [B_156,A_157,C_158] :
      ( r2_hidden(B_156,k1_tops_1(A_157,C_158))
      | ~ m1_connsp_2(C_158,A_157,B_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ m1_subset_1(B_156,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_551,plain,(
    ! [B_156,A_157,A_10] :
      ( r2_hidden(B_156,k1_tops_1(A_157,A_10))
      | ~ m1_connsp_2(A_10,A_157,B_156)
      | ~ m1_subset_1(B_156,u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157)
      | ~ r1_tarski(A_10,u1_struct_0(A_157)) ) ),
    inference(resolution,[status(thm)],[c_12,c_541])).

tff(c_66,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_549,plain,(
    ! [B_156] :
      ( r2_hidden(B_156,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_541])).

tff(c_554,plain,(
    ! [B_156] :
      ( r2_hidden(B_156,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_549])).

tff(c_556,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_159)
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_554])).

tff(c_80,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [B_11,A_68,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_68,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_577,plain,(
    ! [B_11,B_159] :
      ( ~ v1_xboole_0(B_11)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_11)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_159)
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_556,c_85])).

tff(c_631,plain,(
    ! [B_167] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_167)
      | ~ m1_subset_1(B_167,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_644,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_631])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_644])).

tff(c_653,plain,(
    ! [B_168] :
      ( ~ v1_xboole_0(B_168)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_168) ) ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_688,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_71,c_653])).

tff(c_133,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k1_tops_1(A_84,B_85),B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_142,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_138])).

tff(c_180,plain,(
    ! [A_95,B_96] :
      ( v3_pre_topc(k1_tops_1(A_95,B_96),A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_180])).

tff(c_189,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_185])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_153,plain,(
    ! [A_90,B_91,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_92)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_362,plain,(
    ! [A_136,B_137,B_138,B_139] :
      ( r2_hidden('#skF_1'(A_136,B_137),B_138)
      | ~ r1_tarski(B_139,B_138)
      | ~ r1_tarski(A_136,B_139)
      | r1_tarski(A_136,B_137) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_384,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_140,'#skF_4')
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_47,c_362])).

tff(c_401,plain,(
    ! [A_140] :
      ( ~ r1_tarski(A_140,'#skF_4')
      | r1_tarski(A_140,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_689,plain,(
    ! [B_169,A_170,C_171] :
      ( m1_connsp_2(B_169,A_170,C_171)
      | ~ r2_hidden(C_171,B_169)
      | ~ v3_pre_topc(B_169,A_170)
      | ~ m1_subset_1(C_171,u1_struct_0(A_170))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_698,plain,(
    ! [B_169] :
      ( m1_connsp_2(B_169,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_169)
      | ~ v3_pre_topc(B_169,'#skF_2')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_689])).

tff(c_710,plain,(
    ! [B_169] :
      ( m1_connsp_2(B_169,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_169)
      | ~ v3_pre_topc(B_169,'#skF_2')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_698])).

tff(c_753,plain,(
    ! [B_175] :
      ( m1_connsp_2(B_175,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_175)
      | ~ v3_pre_topc(B_175,'#skF_2')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_710])).

tff(c_769,plain,(
    ! [A_176] :
      ( m1_connsp_2(A_176,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_176)
      | ~ v3_pre_topc(A_176,'#skF_2')
      | ~ r1_tarski(A_176,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_753])).

tff(c_827,plain,(
    ! [A_178] :
      ( m1_connsp_2(A_178,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_178)
      | ~ v3_pre_topc(A_178,'#skF_2')
      | ~ r1_tarski(A_178,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_401,c_769])).

tff(c_402,plain,(
    ! [A_142] :
      ( ~ r1_tarski(A_142,'#skF_4')
      | r1_tarski(A_142,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_53,plain,(
    ! [D_57] :
      ( ~ r1_tarski(D_57,'#skF_4')
      | ~ v3_pre_topc(D_57,'#skF_2')
      | ~ m1_connsp_2(D_57,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_61,plain,(
    ! [A_10] :
      ( ~ r1_tarski(A_10,'#skF_4')
      | ~ v3_pre_topc(A_10,'#skF_2')
      | ~ m1_connsp_2(A_10,'#skF_2','#skF_3')
      | v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_421,plain,(
    ! [A_142] :
      ( ~ v3_pre_topc(A_142,'#skF_2')
      | ~ m1_connsp_2(A_142,'#skF_2','#skF_3')
      | v1_xboole_0(A_142)
      | ~ r1_tarski(A_142,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_402,c_61])).

tff(c_863,plain,(
    ! [A_182] :
      ( v1_xboole_0(A_182)
      | ~ r2_hidden('#skF_3',A_182)
      | ~ v3_pre_topc(A_182,'#skF_2')
      | ~ r1_tarski(A_182,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_827,c_421])).

tff(c_870,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_863])).

tff(c_876,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_870])).

tff(c_877,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_876])).

tff(c_880,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_551,c_877])).

tff(c_886,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_40,c_38,c_36,c_32,c_880])).

tff(c_888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.76  
% 3.59/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.76  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.59/1.76  
% 3.59/1.76  %Foreground sorts:
% 3.59/1.76  
% 3.59/1.76  
% 3.59/1.76  %Background operators:
% 3.59/1.76  
% 3.59/1.76  
% 3.59/1.76  %Foreground operators:
% 3.59/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.76  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.59/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.59/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.59/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.59/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.76  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.59/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.76  
% 3.59/1.78  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.59/1.78  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.59/1.78  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.59/1.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.59/1.78  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.59/1.78  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.59/1.78  tff(f_64, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.59/1.78  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.59/1.78  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_43, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/1.78  tff(c_47, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_43])).
% 3.59/1.78  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_32, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/1.78  tff(c_541, plain, (![B_156, A_157, C_158]: (r2_hidden(B_156, k1_tops_1(A_157, C_158)) | ~m1_connsp_2(C_158, A_157, B_156) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~m1_subset_1(B_156, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.59/1.78  tff(c_551, plain, (![B_156, A_157, A_10]: (r2_hidden(B_156, k1_tops_1(A_157, A_10)) | ~m1_connsp_2(A_10, A_157, B_156) | ~m1_subset_1(B_156, u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157) | ~r1_tarski(A_10, u1_struct_0(A_157)))), inference(resolution, [status(thm)], [c_12, c_541])).
% 3.59/1.78  tff(c_66, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.78  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.78  tff(c_71, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_66, c_4])).
% 3.59/1.78  tff(c_549, plain, (![B_156]: (r2_hidden(B_156, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_156) | ~m1_subset_1(B_156, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_541])).
% 3.59/1.78  tff(c_554, plain, (![B_156]: (r2_hidden(B_156, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_156) | ~m1_subset_1(B_156, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_549])).
% 3.59/1.78  tff(c_556, plain, (![B_159]: (r2_hidden(B_159, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_159) | ~m1_subset_1(B_159, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_554])).
% 3.59/1.78  tff(c_80, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.78  tff(c_85, plain, (![B_11, A_68, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_68, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_80])).
% 3.59/1.78  tff(c_577, plain, (![B_11, B_159]: (~v1_xboole_0(B_11) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_11) | ~m1_connsp_2('#skF_4', '#skF_2', B_159) | ~m1_subset_1(B_159, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_556, c_85])).
% 3.59/1.78  tff(c_631, plain, (![B_167]: (~m1_connsp_2('#skF_4', '#skF_2', B_167) | ~m1_subset_1(B_167, u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_577])).
% 3.59/1.78  tff(c_644, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_631])).
% 3.59/1.78  tff(c_651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_644])).
% 3.59/1.78  tff(c_653, plain, (![B_168]: (~v1_xboole_0(B_168) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_168))), inference(splitRight, [status(thm)], [c_577])).
% 3.59/1.78  tff(c_688, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_653])).
% 3.59/1.78  tff(c_133, plain, (![A_84, B_85]: (r1_tarski(k1_tops_1(A_84, B_85), B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.59/1.78  tff(c_138, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_133])).
% 3.59/1.78  tff(c_142, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_138])).
% 3.59/1.78  tff(c_180, plain, (![A_95, B_96]: (v3_pre_topc(k1_tops_1(A_95, B_96), A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.59/1.78  tff(c_185, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_180])).
% 3.59/1.78  tff(c_189, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_185])).
% 3.59/1.78  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.78  tff(c_76, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.78  tff(c_153, plain, (![A_90, B_91, B_92]: (r2_hidden('#skF_1'(A_90, B_91), B_92) | ~r1_tarski(A_90, B_92) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_6, c_76])).
% 3.59/1.78  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.78  tff(c_362, plain, (![A_136, B_137, B_138, B_139]: (r2_hidden('#skF_1'(A_136, B_137), B_138) | ~r1_tarski(B_139, B_138) | ~r1_tarski(A_136, B_139) | r1_tarski(A_136, B_137))), inference(resolution, [status(thm)], [c_153, c_2])).
% 3.59/1.78  tff(c_384, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), u1_struct_0('#skF_2')) | ~r1_tarski(A_140, '#skF_4') | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_47, c_362])).
% 3.59/1.78  tff(c_401, plain, (![A_140]: (~r1_tarski(A_140, '#skF_4') | r1_tarski(A_140, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_384, c_4])).
% 3.59/1.78  tff(c_689, plain, (![B_169, A_170, C_171]: (m1_connsp_2(B_169, A_170, C_171) | ~r2_hidden(C_171, B_169) | ~v3_pre_topc(B_169, A_170) | ~m1_subset_1(C_171, u1_struct_0(A_170)) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.59/1.78  tff(c_698, plain, (![B_169]: (m1_connsp_2(B_169, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_169) | ~v3_pre_topc(B_169, '#skF_2') | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_689])).
% 3.59/1.78  tff(c_710, plain, (![B_169]: (m1_connsp_2(B_169, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_169) | ~v3_pre_topc(B_169, '#skF_2') | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_698])).
% 3.59/1.78  tff(c_753, plain, (![B_175]: (m1_connsp_2(B_175, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_175) | ~v3_pre_topc(B_175, '#skF_2') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_710])).
% 3.59/1.78  tff(c_769, plain, (![A_176]: (m1_connsp_2(A_176, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_176) | ~v3_pre_topc(A_176, '#skF_2') | ~r1_tarski(A_176, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_753])).
% 3.59/1.78  tff(c_827, plain, (![A_178]: (m1_connsp_2(A_178, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_178) | ~v3_pre_topc(A_178, '#skF_2') | ~r1_tarski(A_178, '#skF_4'))), inference(resolution, [status(thm)], [c_401, c_769])).
% 3.59/1.78  tff(c_402, plain, (![A_142]: (~r1_tarski(A_142, '#skF_4') | r1_tarski(A_142, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_384, c_4])).
% 3.59/1.78  tff(c_53, plain, (![D_57]: (~r1_tarski(D_57, '#skF_4') | ~v3_pre_topc(D_57, '#skF_2') | ~m1_connsp_2(D_57, '#skF_2', '#skF_3') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_57))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.59/1.78  tff(c_61, plain, (![A_10]: (~r1_tarski(A_10, '#skF_4') | ~v3_pre_topc(A_10, '#skF_2') | ~m1_connsp_2(A_10, '#skF_2', '#skF_3') | v1_xboole_0(A_10) | ~r1_tarski(A_10, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_53])).
% 3.59/1.78  tff(c_421, plain, (![A_142]: (~v3_pre_topc(A_142, '#skF_2') | ~m1_connsp_2(A_142, '#skF_2', '#skF_3') | v1_xboole_0(A_142) | ~r1_tarski(A_142, '#skF_4'))), inference(resolution, [status(thm)], [c_402, c_61])).
% 3.59/1.78  tff(c_863, plain, (![A_182]: (v1_xboole_0(A_182) | ~r2_hidden('#skF_3', A_182) | ~v3_pre_topc(A_182, '#skF_2') | ~r1_tarski(A_182, '#skF_4'))), inference(resolution, [status(thm)], [c_827, c_421])).
% 3.59/1.78  tff(c_870, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_189, c_863])).
% 3.59/1.78  tff(c_876, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_870])).
% 3.59/1.78  tff(c_877, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_688, c_876])).
% 3.59/1.78  tff(c_880, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_551, c_877])).
% 3.59/1.78  tff(c_886, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_40, c_38, c_36, c_32, c_880])).
% 3.59/1.78  tff(c_888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_886])).
% 3.59/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.78  
% 3.59/1.78  Inference rules
% 3.59/1.78  ----------------------
% 3.59/1.78  #Ref     : 0
% 3.59/1.78  #Sup     : 192
% 3.59/1.78  #Fact    : 0
% 3.59/1.78  #Define  : 0
% 3.59/1.78  #Split   : 8
% 3.59/1.78  #Chain   : 0
% 3.59/1.78  #Close   : 0
% 3.59/1.78  
% 3.59/1.78  Ordering : KBO
% 3.59/1.78  
% 3.59/1.78  Simplification rules
% 3.59/1.78  ----------------------
% 3.59/1.78  #Subsume      : 62
% 3.59/1.78  #Demod        : 47
% 3.59/1.78  #Tautology    : 8
% 3.59/1.78  #SimpNegUnit  : 13
% 3.59/1.78  #BackRed      : 0
% 3.59/1.78  
% 3.59/1.78  #Partial instantiations: 0
% 3.59/1.78  #Strategies tried      : 1
% 3.59/1.78  
% 3.59/1.78  Timing (in seconds)
% 3.59/1.78  ----------------------
% 3.59/1.78  Preprocessing        : 0.48
% 3.59/1.78  Parsing              : 0.24
% 3.59/1.78  CNF conversion       : 0.06
% 3.59/1.78  Main loop            : 0.47
% 3.59/1.78  Inferencing          : 0.17
% 3.59/1.78  Reduction            : 0.12
% 3.59/1.78  Demodulation         : 0.08
% 3.83/1.78  BG Simplification    : 0.03
% 3.83/1.78  Subsumption          : 0.11
% 3.83/1.78  Abstraction          : 0.02
% 3.83/1.78  MUC search           : 0.00
% 3.83/1.78  Cooper               : 0.00
% 3.83/1.78  Total                : 0.99
% 3.83/1.78  Index Insertion      : 0.00
% 3.83/1.78  Index Deletion       : 0.00
% 3.83/1.78  Index Matching       : 0.00
% 3.83/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
