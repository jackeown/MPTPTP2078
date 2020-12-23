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
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 250 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 998 expanded)
%              Number of equality atoms :   10 (  33 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_92,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
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

tff(c_28,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_927,plain,(
    ! [B_121,A_122,C_123] :
      ( r2_hidden(B_121,k1_tops_1(A_122,C_123))
      | ~ m1_connsp_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_121,u1_struct_0(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_932,plain,(
    ! [B_121] :
      ( r2_hidden(B_121,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_121)
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_927])).

tff(c_936,plain,(
    ! [B_121] :
      ( r2_hidden(B_121,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_121)
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_932])).

tff(c_937,plain,(
    ! [B_121] :
      ( r2_hidden(B_121,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_121)
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_936])).

tff(c_938,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_124)
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_936])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_942,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_124)
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_938,c_2])).

tff(c_943,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_942])).

tff(c_72,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tops_1(A_64,B_65),B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_81,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_77])).

tff(c_135,plain,(
    ! [A_74,B_75] :
      ( k1_tops_1(A_74,k1_tops_1(A_74,B_75)) = k1_tops_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_144,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_140])).

tff(c_45,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_68,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_49,c_68])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_64,A_8] :
      ( r1_tarski(k1_tops_1(A_64,A_8),A_8)
      | ~ l1_pre_topc(A_64)
      | ~ r1_tarski(A_8,u1_struct_0(A_64)) ) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_148,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_78])).

tff(c_152,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_154,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_157])).

tff(c_163,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_16,plain,(
    ! [C_27,A_15,D_29,B_23] :
      ( v3_pre_topc(C_27,A_15)
      | k1_tops_1(A_15,C_27) != C_27
      | ~ m1_subset_1(D_29,k1_zfmisc_1(u1_struct_0(B_23)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(B_23)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_642,plain,(
    ! [D_110,B_111] :
      ( ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0(B_111)))
      | ~ l1_pre_topc(B_111) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_649,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_642])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_649])).

tff(c_656,plain,(
    ! [C_112,A_113] :
      ( v3_pre_topc(C_112,A_113)
      | k1_tops_1(A_113,C_112) != C_112
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_736,plain,(
    ! [A_115,A_116] :
      ( v3_pre_topc(A_115,A_116)
      | k1_tops_1(A_116,A_115) != A_115
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ r1_tarski(A_115,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_10,c_656])).

tff(c_752,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_736])).

tff(c_775,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_144,c_752])).

tff(c_1314,plain,(
    ! [C_136,A_137,B_138] :
      ( m1_connsp_2(C_136,A_137,B_138)
      | ~ r2_hidden(B_138,k1_tops_1(A_137,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1324,plain,(
    ! [B_138] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_138)
      | ~ r2_hidden(B_138,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1314])).

tff(c_1342,plain,(
    ! [B_138] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_138)
      | ~ r2_hidden(B_138,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1324])).

tff(c_1343,plain,(
    ! [B_138] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_138)
      | ~ r2_hidden(B_138,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1342])).

tff(c_1345,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1343])).

tff(c_1348,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_1345])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1348])).

tff(c_1389,plain,(
    ! [B_140] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_140)
      | ~ r2_hidden(B_140,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1343])).

tff(c_57,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(A_59,k1_zfmisc_1(B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [D_52] :
      ( ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_connsp_2(D_52,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_90,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_4')
      | ~ v3_pre_topc(A_68,'#skF_2')
      | ~ m1_connsp_2(A_68,'#skF_2','#skF_3')
      | v1_xboole_0(A_68)
      | ~ r1_tarski(A_68,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_97,plain,(
    ! [A_61] :
      ( ~ v3_pre_topc(A_61,'#skF_2')
      | ~ m1_connsp_2(A_61,'#skF_2','#skF_3')
      | v1_xboole_0(A_61)
      | ~ r1_tarski(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_90])).

tff(c_1398,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1389,c_97])).

tff(c_1406,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_81,c_775,c_1398])).

tff(c_1407,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_943,c_1406])).

tff(c_1410,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_937,c_1407])).

tff(c_1414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1410])).

tff(c_1417,plain,(
    ! [B_141] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_141)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_1420,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1417])).

tff(c_1424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:06:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.62  
% 3.74/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.62  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.74/1.62  
% 3.74/1.62  %Foreground sorts:
% 3.74/1.62  
% 3.74/1.62  
% 3.74/1.62  %Background operators:
% 3.74/1.62  
% 3.74/1.62  
% 3.74/1.62  %Foreground operators:
% 3.74/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/1.62  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.74/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.74/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.74/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.74/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.74/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.62  
% 3.74/1.64  tff(f_136, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.74/1.64  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.74/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.74/1.64  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.74/1.64  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 3.74/1.64  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.74/1.64  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.74/1.64  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 3.74/1.64  tff(c_28, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_927, plain, (![B_121, A_122, C_123]: (r2_hidden(B_121, k1_tops_1(A_122, C_123)) | ~m1_connsp_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_121, u1_struct_0(A_122)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.74/1.64  tff(c_932, plain, (![B_121]: (r2_hidden(B_121, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_121) | ~m1_subset_1(B_121, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_927])).
% 3.74/1.64  tff(c_936, plain, (![B_121]: (r2_hidden(B_121, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_121) | ~m1_subset_1(B_121, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_932])).
% 3.74/1.64  tff(c_937, plain, (![B_121]: (r2_hidden(B_121, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_121) | ~m1_subset_1(B_121, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_936])).
% 3.74/1.64  tff(c_938, plain, (![B_124]: (r2_hidden(B_124, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_124) | ~m1_subset_1(B_124, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_936])).
% 3.74/1.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.74/1.64  tff(c_942, plain, (![B_124]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_124) | ~m1_subset_1(B_124, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_938, c_2])).
% 3.74/1.64  tff(c_943, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_942])).
% 3.74/1.64  tff(c_72, plain, (![A_64, B_65]: (r1_tarski(k1_tops_1(A_64, B_65), B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.64  tff(c_77, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_72])).
% 3.74/1.64  tff(c_81, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_77])).
% 3.74/1.64  tff(c_135, plain, (![A_74, B_75]: (k1_tops_1(A_74, k1_tops_1(A_74, B_75))=k1_tops_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.74/1.64  tff(c_140, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_135])).
% 3.74/1.64  tff(c_144, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_140])).
% 3.74/1.64  tff(c_45, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.64  tff(c_49, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_45])).
% 3.74/1.64  tff(c_68, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.64  tff(c_71, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_2')) | ~r1_tarski(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_49, c_68])).
% 3.74/1.64  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.64  tff(c_78, plain, (![A_64, A_8]: (r1_tarski(k1_tops_1(A_64, A_8), A_8) | ~l1_pre_topc(A_64) | ~r1_tarski(A_8, u1_struct_0(A_64)))), inference(resolution, [status(thm)], [c_10, c_72])).
% 3.74/1.64  tff(c_148, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_78])).
% 3.74/1.64  tff(c_152, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_148])).
% 3.74/1.64  tff(c_154, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_152])).
% 3.74/1.64  tff(c_157, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_71, c_154])).
% 3.74/1.64  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_157])).
% 3.74/1.64  tff(c_163, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_152])).
% 3.74/1.64  tff(c_16, plain, (![C_27, A_15, D_29, B_23]: (v3_pre_topc(C_27, A_15) | k1_tops_1(A_15, C_27)!=C_27 | ~m1_subset_1(D_29, k1_zfmisc_1(u1_struct_0(B_23))) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(B_23) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.74/1.64  tff(c_642, plain, (![D_110, B_111]: (~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0(B_111))) | ~l1_pre_topc(B_111))), inference(splitLeft, [status(thm)], [c_16])).
% 3.74/1.64  tff(c_649, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_642])).
% 3.74/1.64  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_649])).
% 3.74/1.64  tff(c_656, plain, (![C_112, A_113]: (v3_pre_topc(C_112, A_113) | k1_tops_1(A_113, C_112)!=C_112 | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(splitRight, [status(thm)], [c_16])).
% 3.74/1.64  tff(c_736, plain, (![A_115, A_116]: (v3_pre_topc(A_115, A_116) | k1_tops_1(A_116, A_115)!=A_115 | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~r1_tarski(A_115, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_10, c_656])).
% 3.74/1.64  tff(c_752, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))!=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_163, c_736])).
% 3.74/1.64  tff(c_775, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_144, c_752])).
% 3.74/1.64  tff(c_1314, plain, (![C_136, A_137, B_138]: (m1_connsp_2(C_136, A_137, B_138) | ~r2_hidden(B_138, k1_tops_1(A_137, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.74/1.64  tff(c_1324, plain, (![B_138]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_138) | ~r2_hidden(B_138, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_138, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1314])).
% 3.74/1.64  tff(c_1342, plain, (![B_138]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_138) | ~r2_hidden(B_138, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_138, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1324])).
% 3.74/1.64  tff(c_1343, plain, (![B_138]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_138) | ~r2_hidden(B_138, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_138, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_1342])).
% 3.74/1.64  tff(c_1345, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1343])).
% 3.74/1.64  tff(c_1348, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_1345])).
% 3.74/1.64  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_1348])).
% 3.74/1.64  tff(c_1389, plain, (![B_140]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_140) | ~r2_hidden(B_140, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_140, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1343])).
% 3.74/1.64  tff(c_57, plain, (![A_59, B_60]: (m1_subset_1(A_59, k1_zfmisc_1(B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.74/1.64  tff(c_26, plain, (![D_52]: (~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_connsp_2(D_52, '#skF_2', '#skF_3') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_52))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.74/1.64  tff(c_90, plain, (![A_68]: (~r1_tarski(A_68, '#skF_4') | ~v3_pre_topc(A_68, '#skF_2') | ~m1_connsp_2(A_68, '#skF_2', '#skF_3') | v1_xboole_0(A_68) | ~r1_tarski(A_68, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_57, c_26])).
% 3.74/1.64  tff(c_97, plain, (![A_61]: (~v3_pre_topc(A_61, '#skF_2') | ~m1_connsp_2(A_61, '#skF_2', '#skF_3') | v1_xboole_0(A_61) | ~r1_tarski(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_90])).
% 3.74/1.64  tff(c_1398, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1389, c_97])).
% 3.74/1.64  tff(c_1406, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_81, c_775, c_1398])).
% 3.74/1.64  tff(c_1407, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_943, c_1406])).
% 3.74/1.64  tff(c_1410, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_937, c_1407])).
% 3.74/1.64  tff(c_1414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1410])).
% 3.74/1.64  tff(c_1417, plain, (![B_141]: (~m1_connsp_2('#skF_4', '#skF_2', B_141) | ~m1_subset_1(B_141, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_942])).
% 3.74/1.64  tff(c_1420, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_1417])).
% 3.74/1.64  tff(c_1424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1420])).
% 3.74/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  Inference rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Ref     : 0
% 3.74/1.64  #Sup     : 295
% 3.74/1.64  #Fact    : 0
% 3.74/1.64  #Define  : 0
% 3.74/1.64  #Split   : 7
% 3.74/1.64  #Chain   : 0
% 3.74/1.64  #Close   : 0
% 3.74/1.64  
% 3.74/1.64  Ordering : KBO
% 3.74/1.64  
% 3.74/1.64  Simplification rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Subsume      : 71
% 3.74/1.64  #Demod        : 350
% 3.74/1.64  #Tautology    : 98
% 3.74/1.64  #SimpNegUnit  : 12
% 3.74/1.64  #BackRed      : 0
% 3.74/1.64  
% 3.74/1.64  #Partial instantiations: 0
% 3.74/1.64  #Strategies tried      : 1
% 3.74/1.64  
% 3.74/1.64  Timing (in seconds)
% 3.74/1.64  ----------------------
% 3.74/1.64  Preprocessing        : 0.32
% 3.74/1.64  Parsing              : 0.19
% 3.74/1.64  CNF conversion       : 0.02
% 3.74/1.64  Main loop            : 0.52
% 3.74/1.64  Inferencing          : 0.17
% 3.74/1.64  Reduction            : 0.16
% 3.74/1.64  Demodulation         : 0.11
% 3.74/1.64  BG Simplification    : 0.02
% 3.74/1.64  Subsumption          : 0.13
% 3.74/1.64  Abstraction          : 0.02
% 3.74/1.64  MUC search           : 0.00
% 3.74/1.65  Cooper               : 0.00
% 3.74/1.65  Total                : 0.89
% 3.74/1.65  Index Insertion      : 0.00
% 3.74/1.65  Index Deletion       : 0.00
% 3.74/1.65  Index Matching       : 0.00
% 3.74/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
