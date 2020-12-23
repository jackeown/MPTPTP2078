%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 370 expanded)
%              Number of leaves         :   28 ( 139 expanded)
%              Depth                    :   18
%              Number of atoms          :  487 (1542 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ! [D] :
                      ( m1_connsp_2(D,A,C)
                     => ~ r1_xboole_0(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ( ~ v2_struct_0(A)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_69,plain,(
    ! [B_96,A_97,C_98] :
      ( r1_xboole_0(B_96,'#skF_1'(A_97,B_96,C_98))
      | r2_hidden(C_98,k2_pre_topc(A_97,B_96))
      | v2_struct_0(A_97)
      | ~ m1_subset_1(C_98,u1_struct_0(A_97))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [C_98] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_98))
      | r2_hidden(C_98,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_98,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_74,plain,(
    ! [C_98] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_98))
      | r2_hidden(C_98,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_98,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_71])).

tff(c_76,plain,(
    ! [C_99] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_99))
      | r2_hidden(C_99,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_99,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_74])).

tff(c_81,plain,
    ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_76,c_54])).

tff(c_87,plain,(
    r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    r1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_116,plain,(
    ! [C_103,A_104,B_105] :
      ( r2_hidden(C_103,'#skF_1'(A_104,B_105,C_103))
      | r2_hidden(C_103,k2_pre_topc(A_104,B_105))
      | v2_struct_0(A_104)
      | ~ m1_subset_1(C_103,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_118,plain,(
    ! [C_103] :
      ( r2_hidden(C_103,'#skF_1'('#skF_3','#skF_4',C_103))
      | r2_hidden(C_103,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_103,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_121,plain,(
    ! [C_103] :
      ( r2_hidden(C_103,'#skF_1'('#skF_3','#skF_4',C_103))
      | r2_hidden(C_103,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_103,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_118])).

tff(c_125,plain,(
    ! [C_110] :
      ( r2_hidden(C_110,'#skF_1'('#skF_3','#skF_4',C_110))
      | r2_hidden(C_110,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_110,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_121])).

tff(c_130,plain,
    ( r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_125,c_54])).

tff(c_136,plain,(
    r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_61,plain,(
    ! [A_92,B_93,C_94] :
      ( v3_pre_topc('#skF_1'(A_92,B_93,C_94),A_92)
      | r2_hidden(C_94,k2_pre_topc(A_92,B_93))
      | v2_struct_0(A_92)
      | ~ m1_subset_1(C_94,u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63,plain,(
    ! [C_94] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_94),'#skF_3')
      | r2_hidden(C_94,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_66,plain,(
    ! [C_94] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_94),'#skF_3')
      | r2_hidden(C_94,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_63])).

tff(c_67,plain,(
    ! [C_94] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_94),'#skF_3')
      | r2_hidden(C_94,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_94,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_66])).

tff(c_178,plain,(
    ! [A_127,B_128,C_129] :
      ( m1_subset_1('#skF_1'(A_127,B_128,C_129),k1_zfmisc_1(u1_struct_0(A_127)))
      | r2_hidden(C_129,k2_pre_topc(A_127,B_128))
      | v2_struct_0(A_127)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_153,plain,(
    ! [B_119,A_120,C_121] :
      ( m1_connsp_2(B_119,A_120,C_121)
      | ~ r2_hidden(C_121,B_119)
      | ~ v3_pre_topc(B_119,A_120)
      | ~ m1_subset_1(C_121,u1_struct_0(A_120))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_155,plain,(
    ! [B_119] :
      ( m1_connsp_2(B_119,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_119)
      | ~ v3_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_158,plain,(
    ! [B_119] :
      ( m1_connsp_2(B_119,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_119)
      | ~ v3_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_155])).

tff(c_159,plain,(
    ! [B_119] :
      ( m1_connsp_2(B_119,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_119)
      | ~ v3_pre_topc(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_158])).

tff(c_182,plain,(
    ! [B_128,C_129] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_128,C_129),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_128,C_129))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_128,C_129),'#skF_3')
      | r2_hidden(C_129,k2_pre_topc('#skF_3',B_128))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_178,c_159])).

tff(c_197,plain,(
    ! [B_128,C_129] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_128,C_129),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_128,C_129))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_128,C_129),'#skF_3')
      | r2_hidden(C_129,k2_pre_topc('#skF_3',B_128))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_182])).

tff(c_348,plain,(
    ! [B_147,C_148] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_147,C_148),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_147,C_148))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_147,C_148),'#skF_3')
      | r2_hidden(C_148,k2_pre_topc('#skF_3',B_147))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_197])).

tff(c_369,plain,(
    ! [C_149] :
      ( m1_connsp_2('#skF_1'('#skF_3','#skF_4',C_149),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_149))
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_149),'#skF_3')
      | r2_hidden(C_149,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_348])).

tff(c_48,plain,(
    ! [D_79] :
      ( r1_xboole_0('#skF_6','#skF_4')
      | ~ r1_xboole_0(D_79,'#skF_4')
      | ~ m1_connsp_2(D_79,'#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    ! [D_79] :
      ( ~ r1_xboole_0(D_79,'#skF_4')
      | ~ m1_connsp_2(D_79,'#skF_3','#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_390,plain,(
    ! [C_154] :
      ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4',C_154),'#skF_4')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_154))
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_154),'#skF_3')
      | r2_hidden(C_154,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_369,c_56])).

tff(c_395,plain,(
    ! [C_155] :
      ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4',C_155),'#skF_4')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_155))
      | r2_hidden(C_155,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_67,c_390])).

tff(c_397,plain,
    ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_136,c_395])).

tff(c_401,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_93,c_397])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_401])).

tff(c_404,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_496,plain,(
    ! [B_189,A_190,C_191] :
      ( r1_xboole_0(B_189,'#skF_1'(A_190,B_189,C_191))
      | r2_hidden(C_191,k2_pre_topc(A_190,B_189))
      | v2_struct_0(A_190)
      | ~ m1_subset_1(C_191,u1_struct_0(A_190))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_498,plain,(
    ! [C_191] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_191))
      | r2_hidden(C_191,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_496])).

tff(c_501,plain,(
    ! [C_191] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_191))
      | r2_hidden(C_191,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_498])).

tff(c_503,plain,(
    ! [C_192] :
      ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4',C_192))
      | r2_hidden(C_192,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_501])).

tff(c_508,plain,
    ( r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_503,c_54])).

tff(c_514,plain,(
    r1_xboole_0('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_508])).

tff(c_520,plain,(
    r1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_514,c_2])).

tff(c_477,plain,(
    ! [C_185,A_186,B_187] :
      ( r2_hidden(C_185,'#skF_1'(A_186,B_187,C_185))
      | r2_hidden(C_185,k2_pre_topc(A_186,B_187))
      | v2_struct_0(A_186)
      | ~ m1_subset_1(C_185,u1_struct_0(A_186))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_479,plain,(
    ! [C_185] :
      ( r2_hidden(C_185,'#skF_1'('#skF_3','#skF_4',C_185))
      | r2_hidden(C_185,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_477])).

tff(c_482,plain,(
    ! [C_185] :
      ( r2_hidden(C_185,'#skF_1'('#skF_3','#skF_4',C_185))
      | r2_hidden(C_185,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_479])).

tff(c_484,plain,(
    ! [C_188] :
      ( r2_hidden(C_188,'#skF_1'('#skF_3','#skF_4',C_188))
      | r2_hidden(C_188,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_482])).

tff(c_489,plain,
    ( r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_484,c_54])).

tff(c_495,plain,(
    r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_489])).

tff(c_469,plain,(
    ! [A_181,B_182,C_183] :
      ( v3_pre_topc('#skF_1'(A_181,B_182,C_183),A_181)
      | r2_hidden(C_183,k2_pre_topc(A_181,B_182))
      | v2_struct_0(A_181)
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_471,plain,(
    ! [C_183] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_183),'#skF_3')
      | r2_hidden(C_183,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_469])).

tff(c_474,plain,(
    ! [C_183] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_183),'#skF_3')
      | r2_hidden(C_183,k2_pre_topc('#skF_3','#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_471])).

tff(c_475,plain,(
    ! [C_183] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_183),'#skF_3')
      | r2_hidden(C_183,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_474])).

tff(c_599,plain,(
    ! [A_216,B_217,C_218] :
      ( m1_subset_1('#skF_1'(A_216,B_217,C_218),k1_zfmisc_1(u1_struct_0(A_216)))
      | r2_hidden(C_218,k2_pre_topc(A_216,B_217))
      | v2_struct_0(A_216)
      | ~ m1_subset_1(C_218,u1_struct_0(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_528,plain,(
    ! [B_193,A_194,C_195] :
      ( m1_connsp_2(B_193,A_194,C_195)
      | ~ r2_hidden(C_195,B_193)
      | ~ v3_pre_topc(B_193,A_194)
      | ~ m1_subset_1(C_195,u1_struct_0(A_194))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_530,plain,(
    ! [B_193] :
      ( m1_connsp_2(B_193,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_193)
      | ~ v3_pre_topc(B_193,'#skF_3')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_528])).

tff(c_533,plain,(
    ! [B_193] :
      ( m1_connsp_2(B_193,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_193)
      | ~ v3_pre_topc(B_193,'#skF_3')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_530])).

tff(c_534,plain,(
    ! [B_193] :
      ( m1_connsp_2(B_193,'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5',B_193)
      | ~ v3_pre_topc(B_193,'#skF_3')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_533])).

tff(c_609,plain,(
    ! [B_217,C_218] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_217,C_218),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_217,C_218))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_217,C_218),'#skF_3')
      | r2_hidden(C_218,k2_pre_topc('#skF_3',B_217))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_599,c_534])).

tff(c_621,plain,(
    ! [B_217,C_218] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_217,C_218),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_217,C_218))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_217,C_218),'#skF_3')
      | r2_hidden(C_218,k2_pre_topc('#skF_3',B_217))
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_609])).

tff(c_779,plain,(
    ! [B_236,C_237] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_236,C_237),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3',B_236,C_237))
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_236,C_237),'#skF_3')
      | r2_hidden(C_237,k2_pre_topc('#skF_3',B_236))
      | ~ m1_subset_1(C_237,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_621])).

tff(c_800,plain,(
    ! [C_238] :
      ( m1_connsp_2('#skF_1'('#skF_3','#skF_4',C_238),'#skF_3','#skF_5')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_238))
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_238),'#skF_3')
      | r2_hidden(C_238,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_238,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_779])).

tff(c_50,plain,(
    ! [D_79] :
      ( m1_connsp_2('#skF_6','#skF_3','#skF_5')
      | ~ r1_xboole_0(D_79,'#skF_4')
      | ~ m1_connsp_2(D_79,'#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_411,plain,(
    ! [D_79] :
      ( ~ r1_xboole_0(D_79,'#skF_4')
      | ~ m1_connsp_2(D_79,'#skF_3','#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_811,plain,(
    ! [C_239] :
      ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4',C_239),'#skF_4')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_239))
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',C_239),'#skF_3')
      | r2_hidden(C_239,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_239,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_800,c_411])).

tff(c_816,plain,(
    ! [C_240] :
      ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4',C_240),'#skF_4')
      | ~ r2_hidden('#skF_5','#skF_1'('#skF_3','#skF_4',C_240))
      | r2_hidden(C_240,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_475,c_811])).

tff(c_818,plain,
    ( ~ r1_xboole_0('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_495,c_816])).

tff(c_822,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_520,c_818])).

tff(c_824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_822])).

tff(c_825,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,(
    ! [D_79] :
      ( r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_xboole_0(D_79,'#skF_4')
      | ~ m1_connsp_2(D_79,'#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_834,plain,(
    ! [D_241] :
      ( ~ r1_xboole_0(D_241,'#skF_4')
      | ~ m1_connsp_2(D_241,'#skF_3','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52])).

tff(c_837,plain,(
    ~ r1_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_825,c_834])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_837])).

tff(c_843,plain,(
    r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_852,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_44])).

tff(c_915,plain,(
    ! [C_266,A_267,B_268] :
      ( m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ m1_connsp_2(C_266,A_267,B_268)
      | ~ m1_subset_1(B_268,u1_struct_0(A_267))
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_917,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_852,c_915])).

tff(c_920,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_917])).

tff(c_921,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_920])).

tff(c_975,plain,(
    ! [A_282,B_283,C_284] :
      ( r1_tarski('#skF_2'(A_282,B_283,C_284),C_284)
      | ~ m1_connsp_2(C_284,A_282,B_283)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(B_283,u1_struct_0(A_282))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_977,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_2'('#skF_3',B_283,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_283)
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_921,c_975])).

tff(c_982,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_2'('#skF_3',B_283,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_283)
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_977])).

tff(c_983,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_2'('#skF_3',B_283,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_283)
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_982])).

tff(c_1063,plain,(
    ! [A_298,B_299,C_300] :
      ( v3_pre_topc('#skF_2'(A_298,B_299,C_300),A_298)
      | ~ m1_connsp_2(C_300,A_298,B_299)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m1_subset_1(B_299,u1_struct_0(A_298))
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1065,plain,(
    ! [B_299] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_299,'#skF_6'),'#skF_3')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_299)
      | ~ m1_subset_1(B_299,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_921,c_1063])).

tff(c_1070,plain,(
    ! [B_299] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_299,'#skF_6'),'#skF_3')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_299)
      | ~ m1_subset_1(B_299,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1065])).

tff(c_1071,plain,(
    ! [B_299] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_299,'#skF_6'),'#skF_3')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_299)
      | ~ m1_subset_1(B_299,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1070])).

tff(c_30,plain,(
    ! [A_39,B_51,C_57] :
      ( m1_subset_1('#skF_2'(A_39,B_51,C_57),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_connsp_2(C_57,A_39,B_51)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_subset_1(B_51,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1029,plain,(
    ! [B_289,A_290,C_291] :
      ( r2_hidden(B_289,'#skF_2'(A_290,B_289,C_291))
      | ~ m1_connsp_2(C_291,A_290,B_289)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ m1_subset_1(B_289,u1_struct_0(A_290))
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1031,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,'#skF_2'('#skF_3',B_289,'#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_921,c_1029])).

tff(c_1036,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,'#skF_2'('#skF_3',B_289,'#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1031])).

tff(c_1037,plain,(
    ! [B_289] :
      ( r2_hidden(B_289,'#skF_2'('#skF_3',B_289,'#skF_6'))
      | ~ m1_connsp_2('#skF_6','#skF_3',B_289)
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1036])).

tff(c_842,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_853,plain,(
    ! [A_242,C_243,B_244] :
      ( r1_xboole_0(A_242,C_243)
      | ~ r1_xboole_0(B_244,C_243)
      | ~ r1_tarski(A_242,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_860,plain,(
    ! [A_245] :
      ( r1_xboole_0(A_245,'#skF_4')
      | ~ r1_tarski(A_245,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_842,c_853])).

tff(c_866,plain,(
    ! [A_245] :
      ( r1_xboole_0('#skF_4',A_245)
      | ~ r1_tarski(A_245,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_860,c_2])).

tff(c_1132,plain,(
    ! [B_309,D_310,C_311,A_312] :
      ( ~ r1_xboole_0(B_309,D_310)
      | ~ r2_hidden(C_311,D_310)
      | ~ v3_pre_topc(D_310,A_312)
      | ~ m1_subset_1(D_310,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ r2_hidden(C_311,k2_pre_topc(A_312,B_309))
      | ~ m1_subset_1(C_311,u1_struct_0(A_312))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1339,plain,(
    ! [C_335,A_336,A_337] :
      ( ~ r2_hidden(C_335,A_336)
      | ~ v3_pre_topc(A_336,A_337)
      | ~ m1_subset_1(A_336,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ r2_hidden(C_335,k2_pre_topc(A_337,'#skF_4'))
      | ~ m1_subset_1(C_335,u1_struct_0(A_337))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337)
      | ~ r1_tarski(A_336,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_866,c_1132])).

tff(c_2268,plain,(
    ! [B_499,A_500] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3',B_499,'#skF_6'),A_500)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_499,'#skF_6'),k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ r2_hidden(B_499,k2_pre_topc(A_500,'#skF_4'))
      | ~ m1_subset_1(B_499,u1_struct_0(A_500))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ l1_pre_topc(A_500)
      | ~ r1_tarski('#skF_2'('#skF_3',B_499,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_499)
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1037,c_1339])).

tff(c_2275,plain,(
    ! [B_51] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3',B_51,'#skF_6'),'#skF_3')
      | ~ r2_hidden(B_51,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_2'('#skF_3',B_51,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_51)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_2268])).

tff(c_2281,plain,(
    ! [B_51] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3',B_51,'#skF_6'),'#skF_3')
      | ~ r2_hidden(B_51,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_51,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_921,c_34,c_2275])).

tff(c_2283,plain,(
    ! [B_501] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3',B_501,'#skF_6'),'#skF_3')
      | ~ r2_hidden(B_501,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_501,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2281])).

tff(c_2288,plain,(
    ! [B_502] :
      ( ~ r2_hidden(B_502,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_3',B_502,'#skF_6'),'#skF_6')
      | ~ m1_connsp_2('#skF_6','#skF_3',B_502)
      | ~ m1_subset_1(B_502,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1071,c_2283])).

tff(c_2297,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_6')
    | ~ m1_connsp_2('#skF_6','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_843,c_2288])).

tff(c_2302,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_852,c_2297])).

tff(c_2305,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_983,c_2302])).

tff(c_2309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_852,c_2305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.09  
% 5.80/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.10  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.80/2.10  
% 5.80/2.10  %Foreground sorts:
% 5.80/2.10  
% 5.80/2.10  
% 5.80/2.10  %Background operators:
% 5.80/2.10  
% 5.80/2.10  
% 5.80/2.10  %Foreground operators:
% 5.80/2.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.80/2.10  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.80/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.80/2.10  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.80/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.80/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.80/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.80/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.80/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.80/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.80/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.80/2.10  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.80/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.10  
% 6.01/2.13  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_connsp_2(D, A, C) => ~r1_xboole_0(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_connsp_2)).
% 6.01/2.13  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 6.01/2.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.01/2.13  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 6.01/2.13  tff(f_72, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 6.01/2.13  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.01/2.13  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.01/2.13  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_42, plain, (r1_xboole_0('#skF_6', '#skF_4') | ~r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_54, plain, (~r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 6.01/2.13  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_69, plain, (![B_96, A_97, C_98]: (r1_xboole_0(B_96, '#skF_1'(A_97, B_96, C_98)) | r2_hidden(C_98, k2_pre_topc(A_97, B_96)) | v2_struct_0(A_97) | ~m1_subset_1(C_98, u1_struct_0(A_97)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_71, plain, (![C_98]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_98)) | r2_hidden(C_98, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_98, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_69])).
% 6.01/2.13  tff(c_74, plain, (![C_98]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_98)) | r2_hidden(C_98, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_98, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_71])).
% 6.01/2.13  tff(c_76, plain, (![C_99]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_99)) | r2_hidden(C_99, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_99, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_74])).
% 6.01/2.13  tff(c_81, plain, (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_76, c_54])).
% 6.01/2.13  tff(c_87, plain, (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_81])).
% 6.01/2.13  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.01/2.13  tff(c_93, plain, (r1_xboole_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_87, c_2])).
% 6.01/2.13  tff(c_116, plain, (![C_103, A_104, B_105]: (r2_hidden(C_103, '#skF_1'(A_104, B_105, C_103)) | r2_hidden(C_103, k2_pre_topc(A_104, B_105)) | v2_struct_0(A_104) | ~m1_subset_1(C_103, u1_struct_0(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_118, plain, (![C_103]: (r2_hidden(C_103, '#skF_1'('#skF_3', '#skF_4', C_103)) | r2_hidden(C_103, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_103, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_116])).
% 6.01/2.13  tff(c_121, plain, (![C_103]: (r2_hidden(C_103, '#skF_1'('#skF_3', '#skF_4', C_103)) | r2_hidden(C_103, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_103, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_118])).
% 6.01/2.13  tff(c_125, plain, (![C_110]: (r2_hidden(C_110, '#skF_1'('#skF_3', '#skF_4', C_110)) | r2_hidden(C_110, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_110, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_121])).
% 6.01/2.13  tff(c_130, plain, (r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_125, c_54])).
% 6.01/2.13  tff(c_136, plain, (r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130])).
% 6.01/2.13  tff(c_61, plain, (![A_92, B_93, C_94]: (v3_pre_topc('#skF_1'(A_92, B_93, C_94), A_92) | r2_hidden(C_94, k2_pre_topc(A_92, B_93)) | v2_struct_0(A_92) | ~m1_subset_1(C_94, u1_struct_0(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_63, plain, (![C_94]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_94), '#skF_3') | r2_hidden(C_94, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_94, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_61])).
% 6.01/2.13  tff(c_66, plain, (![C_94]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_94), '#skF_3') | r2_hidden(C_94, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_94, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_63])).
% 6.01/2.13  tff(c_67, plain, (![C_94]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_94), '#skF_3') | r2_hidden(C_94, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_94, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_66])).
% 6.01/2.13  tff(c_178, plain, (![A_127, B_128, C_129]: (m1_subset_1('#skF_1'(A_127, B_128, C_129), k1_zfmisc_1(u1_struct_0(A_127))) | r2_hidden(C_129, k2_pre_topc(A_127, B_128)) | v2_struct_0(A_127) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_153, plain, (![B_119, A_120, C_121]: (m1_connsp_2(B_119, A_120, C_121) | ~r2_hidden(C_121, B_119) | ~v3_pre_topc(B_119, A_120) | ~m1_subset_1(C_121, u1_struct_0(A_120)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.01/2.13  tff(c_155, plain, (![B_119]: (m1_connsp_2(B_119, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_119) | ~v3_pre_topc(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_153])).
% 6.01/2.13  tff(c_158, plain, (![B_119]: (m1_connsp_2(B_119, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_119) | ~v3_pre_topc(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_155])).
% 6.01/2.13  tff(c_159, plain, (![B_119]: (m1_connsp_2(B_119, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_119) | ~v3_pre_topc(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_158])).
% 6.01/2.13  tff(c_182, plain, (![B_128, C_129]: (m1_connsp_2('#skF_1'('#skF_3', B_128, C_129), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_128, C_129)) | ~v3_pre_topc('#skF_1'('#skF_3', B_128, C_129), '#skF_3') | r2_hidden(C_129, k2_pre_topc('#skF_3', B_128)) | v2_struct_0('#skF_3') | ~m1_subset_1(C_129, u1_struct_0('#skF_3')) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_159])).
% 6.01/2.13  tff(c_197, plain, (![B_128, C_129]: (m1_connsp_2('#skF_1'('#skF_3', B_128, C_129), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_128, C_129)) | ~v3_pre_topc('#skF_1'('#skF_3', B_128, C_129), '#skF_3') | r2_hidden(C_129, k2_pre_topc('#skF_3', B_128)) | v2_struct_0('#skF_3') | ~m1_subset_1(C_129, u1_struct_0('#skF_3')) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_182])).
% 6.01/2.13  tff(c_348, plain, (![B_147, C_148]: (m1_connsp_2('#skF_1'('#skF_3', B_147, C_148), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_147, C_148)) | ~v3_pre_topc('#skF_1'('#skF_3', B_147, C_148), '#skF_3') | r2_hidden(C_148, k2_pre_topc('#skF_3', B_147)) | ~m1_subset_1(C_148, u1_struct_0('#skF_3')) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_197])).
% 6.01/2.13  tff(c_369, plain, (![C_149]: (m1_connsp_2('#skF_1'('#skF_3', '#skF_4', C_149), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_149)) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_149), '#skF_3') | r2_hidden(C_149, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_149, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_348])).
% 6.01/2.13  tff(c_48, plain, (![D_79]: (r1_xboole_0('#skF_6', '#skF_4') | ~r1_xboole_0(D_79, '#skF_4') | ~m1_connsp_2(D_79, '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_56, plain, (![D_79]: (~r1_xboole_0(D_79, '#skF_4') | ~m1_connsp_2(D_79, '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.01/2.13  tff(c_390, plain, (![C_154]: (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', C_154), '#skF_4') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_154)) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_154), '#skF_3') | r2_hidden(C_154, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_154, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_369, c_56])).
% 6.01/2.13  tff(c_395, plain, (![C_155]: (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', C_155), '#skF_4') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_155)) | r2_hidden(C_155, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_155, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_67, c_390])).
% 6.01/2.13  tff(c_397, plain, (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_136, c_395])).
% 6.01/2.13  tff(c_401, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_93, c_397])).
% 6.01/2.13  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_401])).
% 6.01/2.13  tff(c_404, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 6.01/2.13  tff(c_496, plain, (![B_189, A_190, C_191]: (r1_xboole_0(B_189, '#skF_1'(A_190, B_189, C_191)) | r2_hidden(C_191, k2_pre_topc(A_190, B_189)) | v2_struct_0(A_190) | ~m1_subset_1(C_191, u1_struct_0(A_190)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_498, plain, (![C_191]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_191)) | r2_hidden(C_191, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_191, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_496])).
% 6.01/2.13  tff(c_501, plain, (![C_191]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_191)) | r2_hidden(C_191, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_191, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_498])).
% 6.01/2.13  tff(c_503, plain, (![C_192]: (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', C_192)) | r2_hidden(C_192, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_192, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_501])).
% 6.01/2.13  tff(c_508, plain, (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_503, c_54])).
% 6.01/2.13  tff(c_514, plain, (r1_xboole_0('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_508])).
% 6.01/2.13  tff(c_520, plain, (r1_xboole_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_514, c_2])).
% 6.01/2.13  tff(c_477, plain, (![C_185, A_186, B_187]: (r2_hidden(C_185, '#skF_1'(A_186, B_187, C_185)) | r2_hidden(C_185, k2_pre_topc(A_186, B_187)) | v2_struct_0(A_186) | ~m1_subset_1(C_185, u1_struct_0(A_186)) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_479, plain, (![C_185]: (r2_hidden(C_185, '#skF_1'('#skF_3', '#skF_4', C_185)) | r2_hidden(C_185, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_185, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_477])).
% 6.01/2.13  tff(c_482, plain, (![C_185]: (r2_hidden(C_185, '#skF_1'('#skF_3', '#skF_4', C_185)) | r2_hidden(C_185, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_185, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_479])).
% 6.01/2.13  tff(c_484, plain, (![C_188]: (r2_hidden(C_188, '#skF_1'('#skF_3', '#skF_4', C_188)) | r2_hidden(C_188, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_188, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_482])).
% 6.01/2.13  tff(c_489, plain, (r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_484, c_54])).
% 6.01/2.13  tff(c_495, plain, (r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_489])).
% 6.01/2.13  tff(c_469, plain, (![A_181, B_182, C_183]: (v3_pre_topc('#skF_1'(A_181, B_182, C_183), A_181) | r2_hidden(C_183, k2_pre_topc(A_181, B_182)) | v2_struct_0(A_181) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_471, plain, (![C_183]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_183), '#skF_3') | r2_hidden(C_183, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_183, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_469])).
% 6.01/2.13  tff(c_474, plain, (![C_183]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_183), '#skF_3') | r2_hidden(C_183, k2_pre_topc('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | ~m1_subset_1(C_183, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_471])).
% 6.01/2.13  tff(c_475, plain, (![C_183]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_183), '#skF_3') | r2_hidden(C_183, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_183, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_474])).
% 6.01/2.13  tff(c_599, plain, (![A_216, B_217, C_218]: (m1_subset_1('#skF_1'(A_216, B_217, C_218), k1_zfmisc_1(u1_struct_0(A_216))) | r2_hidden(C_218, k2_pre_topc(A_216, B_217)) | v2_struct_0(A_216) | ~m1_subset_1(C_218, u1_struct_0(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_528, plain, (![B_193, A_194, C_195]: (m1_connsp_2(B_193, A_194, C_195) | ~r2_hidden(C_195, B_193) | ~v3_pre_topc(B_193, A_194) | ~m1_subset_1(C_195, u1_struct_0(A_194)) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.01/2.13  tff(c_530, plain, (![B_193]: (m1_connsp_2(B_193, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_193) | ~v3_pre_topc(B_193, '#skF_3') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_528])).
% 6.01/2.13  tff(c_533, plain, (![B_193]: (m1_connsp_2(B_193, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_193) | ~v3_pre_topc(B_193, '#skF_3') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_530])).
% 6.01/2.13  tff(c_534, plain, (![B_193]: (m1_connsp_2(B_193, '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', B_193) | ~v3_pre_topc(B_193, '#skF_3') | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_533])).
% 6.01/2.13  tff(c_609, plain, (![B_217, C_218]: (m1_connsp_2('#skF_1'('#skF_3', B_217, C_218), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_217, C_218)) | ~v3_pre_topc('#skF_1'('#skF_3', B_217, C_218), '#skF_3') | r2_hidden(C_218, k2_pre_topc('#skF_3', B_217)) | v2_struct_0('#skF_3') | ~m1_subset_1(C_218, u1_struct_0('#skF_3')) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_599, c_534])).
% 6.01/2.13  tff(c_621, plain, (![B_217, C_218]: (m1_connsp_2('#skF_1'('#skF_3', B_217, C_218), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_217, C_218)) | ~v3_pre_topc('#skF_1'('#skF_3', B_217, C_218), '#skF_3') | r2_hidden(C_218, k2_pre_topc('#skF_3', B_217)) | v2_struct_0('#skF_3') | ~m1_subset_1(C_218, u1_struct_0('#skF_3')) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_609])).
% 6.01/2.13  tff(c_779, plain, (![B_236, C_237]: (m1_connsp_2('#skF_1'('#skF_3', B_236, C_237), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', B_236, C_237)) | ~v3_pre_topc('#skF_1'('#skF_3', B_236, C_237), '#skF_3') | r2_hidden(C_237, k2_pre_topc('#skF_3', B_236)) | ~m1_subset_1(C_237, u1_struct_0('#skF_3')) | ~m1_subset_1(B_236, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_621])).
% 6.01/2.13  tff(c_800, plain, (![C_238]: (m1_connsp_2('#skF_1'('#skF_3', '#skF_4', C_238), '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_238)) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_238), '#skF_3') | r2_hidden(C_238, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_238, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_779])).
% 6.01/2.13  tff(c_50, plain, (![D_79]: (m1_connsp_2('#skF_6', '#skF_3', '#skF_5') | ~r1_xboole_0(D_79, '#skF_4') | ~m1_connsp_2(D_79, '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_411, plain, (![D_79]: (~r1_xboole_0(D_79, '#skF_4') | ~m1_connsp_2(D_79, '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_50])).
% 6.01/2.13  tff(c_811, plain, (![C_239]: (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', C_239), '#skF_4') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_239)) | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', C_239), '#skF_3') | r2_hidden(C_239, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_239, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_800, c_411])).
% 6.01/2.13  tff(c_816, plain, (![C_240]: (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', C_240), '#skF_4') | ~r2_hidden('#skF_5', '#skF_1'('#skF_3', '#skF_4', C_240)) | r2_hidden(C_240, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1(C_240, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_475, c_811])).
% 6.01/2.13  tff(c_818, plain, (~r1_xboole_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_495, c_816])).
% 6.01/2.13  tff(c_822, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_520, c_818])).
% 6.01/2.13  tff(c_824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_822])).
% 6.01/2.13  tff(c_825, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 6.01/2.13  tff(c_52, plain, (![D_79]: (r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4')) | ~r1_xboole_0(D_79, '#skF_4') | ~m1_connsp_2(D_79, '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_834, plain, (![D_241]: (~r1_xboole_0(D_241, '#skF_4') | ~m1_connsp_2(D_241, '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_52])).
% 6.01/2.13  tff(c_837, plain, (~r1_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_825, c_834])).
% 6.01/2.13  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_837])).
% 6.01/2.13  tff(c_843, plain, (r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 6.01/2.13  tff(c_44, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_5') | ~r2_hidden('#skF_5', k2_pre_topc('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.01/2.13  tff(c_852, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_44])).
% 6.01/2.13  tff(c_915, plain, (![C_266, A_267, B_268]: (m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~m1_connsp_2(C_266, A_267, B_268) | ~m1_subset_1(B_268, u1_struct_0(A_267)) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.01/2.13  tff(c_917, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_852, c_915])).
% 6.01/2.13  tff(c_920, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_917])).
% 6.01/2.13  tff(c_921, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_920])).
% 6.01/2.13  tff(c_975, plain, (![A_282, B_283, C_284]: (r1_tarski('#skF_2'(A_282, B_283, C_284), C_284) | ~m1_connsp_2(C_284, A_282, B_283) | ~m1_subset_1(C_284, k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(B_283, u1_struct_0(A_282)) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.01/2.13  tff(c_977, plain, (![B_283]: (r1_tarski('#skF_2'('#skF_3', B_283, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_283) | ~m1_subset_1(B_283, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_921, c_975])).
% 6.01/2.13  tff(c_982, plain, (![B_283]: (r1_tarski('#skF_2'('#skF_3', B_283, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_283) | ~m1_subset_1(B_283, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_977])).
% 6.01/2.13  tff(c_983, plain, (![B_283]: (r1_tarski('#skF_2'('#skF_3', B_283, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_283) | ~m1_subset_1(B_283, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_982])).
% 6.01/2.13  tff(c_1063, plain, (![A_298, B_299, C_300]: (v3_pre_topc('#skF_2'(A_298, B_299, C_300), A_298) | ~m1_connsp_2(C_300, A_298, B_299) | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0(A_298))) | ~m1_subset_1(B_299, u1_struct_0(A_298)) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.01/2.13  tff(c_1065, plain, (![B_299]: (v3_pre_topc('#skF_2'('#skF_3', B_299, '#skF_6'), '#skF_3') | ~m1_connsp_2('#skF_6', '#skF_3', B_299) | ~m1_subset_1(B_299, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_921, c_1063])).
% 6.01/2.13  tff(c_1070, plain, (![B_299]: (v3_pre_topc('#skF_2'('#skF_3', B_299, '#skF_6'), '#skF_3') | ~m1_connsp_2('#skF_6', '#skF_3', B_299) | ~m1_subset_1(B_299, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1065])).
% 6.01/2.13  tff(c_1071, plain, (![B_299]: (v3_pre_topc('#skF_2'('#skF_3', B_299, '#skF_6'), '#skF_3') | ~m1_connsp_2('#skF_6', '#skF_3', B_299) | ~m1_subset_1(B_299, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1070])).
% 6.01/2.13  tff(c_30, plain, (![A_39, B_51, C_57]: (m1_subset_1('#skF_2'(A_39, B_51, C_57), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_connsp_2(C_57, A_39, B_51) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_subset_1(B_51, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.01/2.13  tff(c_1029, plain, (![B_289, A_290, C_291]: (r2_hidden(B_289, '#skF_2'(A_290, B_289, C_291)) | ~m1_connsp_2(C_291, A_290, B_289) | ~m1_subset_1(C_291, k1_zfmisc_1(u1_struct_0(A_290))) | ~m1_subset_1(B_289, u1_struct_0(A_290)) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.01/2.13  tff(c_1031, plain, (![B_289]: (r2_hidden(B_289, '#skF_2'('#skF_3', B_289, '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_289) | ~m1_subset_1(B_289, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_921, c_1029])).
% 6.01/2.13  tff(c_1036, plain, (![B_289]: (r2_hidden(B_289, '#skF_2'('#skF_3', B_289, '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_289) | ~m1_subset_1(B_289, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1031])).
% 6.01/2.13  tff(c_1037, plain, (![B_289]: (r2_hidden(B_289, '#skF_2'('#skF_3', B_289, '#skF_6')) | ~m1_connsp_2('#skF_6', '#skF_3', B_289) | ~m1_subset_1(B_289, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1036])).
% 6.01/2.13  tff(c_842, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 6.01/2.13  tff(c_853, plain, (![A_242, C_243, B_244]: (r1_xboole_0(A_242, C_243) | ~r1_xboole_0(B_244, C_243) | ~r1_tarski(A_242, B_244))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.01/2.13  tff(c_860, plain, (![A_245]: (r1_xboole_0(A_245, '#skF_4') | ~r1_tarski(A_245, '#skF_6'))), inference(resolution, [status(thm)], [c_842, c_853])).
% 6.01/2.13  tff(c_866, plain, (![A_245]: (r1_xboole_0('#skF_4', A_245) | ~r1_tarski(A_245, '#skF_6'))), inference(resolution, [status(thm)], [c_860, c_2])).
% 6.01/2.13  tff(c_1132, plain, (![B_309, D_310, C_311, A_312]: (~r1_xboole_0(B_309, D_310) | ~r2_hidden(C_311, D_310) | ~v3_pre_topc(D_310, A_312) | ~m1_subset_1(D_310, k1_zfmisc_1(u1_struct_0(A_312))) | ~r2_hidden(C_311, k2_pre_topc(A_312, B_309)) | ~m1_subset_1(C_311, u1_struct_0(A_312)) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.13  tff(c_1339, plain, (![C_335, A_336, A_337]: (~r2_hidden(C_335, A_336) | ~v3_pre_topc(A_336, A_337) | ~m1_subset_1(A_336, k1_zfmisc_1(u1_struct_0(A_337))) | ~r2_hidden(C_335, k2_pre_topc(A_337, '#skF_4')) | ~m1_subset_1(C_335, u1_struct_0(A_337)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337) | ~r1_tarski(A_336, '#skF_6'))), inference(resolution, [status(thm)], [c_866, c_1132])).
% 6.01/2.13  tff(c_2268, plain, (![B_499, A_500]: (~v3_pre_topc('#skF_2'('#skF_3', B_499, '#skF_6'), A_500) | ~m1_subset_1('#skF_2'('#skF_3', B_499, '#skF_6'), k1_zfmisc_1(u1_struct_0(A_500))) | ~r2_hidden(B_499, k2_pre_topc(A_500, '#skF_4')) | ~m1_subset_1(B_499, u1_struct_0(A_500)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_500))) | ~l1_pre_topc(A_500) | ~r1_tarski('#skF_2'('#skF_3', B_499, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_499) | ~m1_subset_1(B_499, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1037, c_1339])).
% 6.01/2.13  tff(c_2275, plain, (![B_51]: (~v3_pre_topc('#skF_2'('#skF_3', B_51, '#skF_6'), '#skF_3') | ~r2_hidden(B_51, k2_pre_topc('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_2'('#skF_3', B_51, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_51) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_2268])).
% 6.01/2.13  tff(c_2281, plain, (![B_51]: (~v3_pre_topc('#skF_2'('#skF_3', B_51, '#skF_6'), '#skF_3') | ~r2_hidden(B_51, k2_pre_topc('#skF_3', '#skF_4')) | ~r1_tarski('#skF_2'('#skF_3', B_51, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_921, c_34, c_2275])).
% 6.01/2.13  tff(c_2283, plain, (![B_501]: (~v3_pre_topc('#skF_2'('#skF_3', B_501, '#skF_6'), '#skF_3') | ~r2_hidden(B_501, k2_pre_topc('#skF_3', '#skF_4')) | ~r1_tarski('#skF_2'('#skF_3', B_501, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_2281])).
% 6.01/2.13  tff(c_2288, plain, (![B_502]: (~r2_hidden(B_502, k2_pre_topc('#skF_3', '#skF_4')) | ~r1_tarski('#skF_2'('#skF_3', B_502, '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', B_502) | ~m1_subset_1(B_502, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1071, c_2283])).
% 6.01/2.13  tff(c_2297, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_6') | ~m1_connsp_2('#skF_6', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_843, c_2288])).
% 6.01/2.13  tff(c_2302, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_852, c_2297])).
% 6.01/2.13  tff(c_2305, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_983, c_2302])).
% 6.01/2.13  tff(c_2309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_852, c_2305])).
% 6.01/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.13  
% 6.01/2.13  Inference rules
% 6.01/2.13  ----------------------
% 6.01/2.13  #Ref     : 0
% 6.01/2.13  #Sup     : 531
% 6.01/2.13  #Fact    : 0
% 6.01/2.13  #Define  : 0
% 6.01/2.13  #Split   : 21
% 6.01/2.13  #Chain   : 0
% 6.01/2.13  #Close   : 0
% 6.01/2.13  
% 6.01/2.13  Ordering : KBO
% 6.01/2.13  
% 6.01/2.13  Simplification rules
% 6.01/2.13  ----------------------
% 6.01/2.13  #Subsume      : 72
% 6.01/2.13  #Demod        : 228
% 6.01/2.13  #Tautology    : 15
% 6.01/2.13  #SimpNegUnit  : 100
% 6.01/2.13  #BackRed      : 0
% 6.01/2.13  
% 6.01/2.13  #Partial instantiations: 0
% 6.01/2.13  #Strategies tried      : 1
% 6.01/2.13  
% 6.01/2.13  Timing (in seconds)
% 6.01/2.13  ----------------------
% 6.01/2.13  Preprocessing        : 0.32
% 6.01/2.13  Parsing              : 0.17
% 6.01/2.13  CNF conversion       : 0.03
% 6.01/2.13  Main loop            : 1.03
% 6.01/2.13  Inferencing          : 0.36
% 6.01/2.13  Reduction            : 0.25
% 6.01/2.13  Demodulation         : 0.16
% 6.01/2.13  BG Simplification    : 0.04
% 6.01/2.13  Subsumption          : 0.32
% 6.01/2.13  Abstraction          : 0.04
% 6.01/2.13  MUC search           : 0.00
% 6.01/2.13  Cooper               : 0.00
% 6.01/2.13  Total                : 1.40
% 6.01/2.13  Index Insertion      : 0.00
% 6.01/2.13  Index Deletion       : 0.00
% 6.01/2.13  Index Matching       : 0.00
% 6.01/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
