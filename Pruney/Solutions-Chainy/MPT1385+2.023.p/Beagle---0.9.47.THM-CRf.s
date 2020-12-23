%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 287 expanded)
%              Number of leaves         :   33 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  273 ( 922 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_72,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_65,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_235,plain,(
    ! [B_109,A_110,C_111] :
      ( r2_hidden(B_109,k1_tops_1(A_110,C_111))
      | ~ m1_connsp_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(B_109,u1_struct_0(A_110))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_242,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_235])).

tff(c_247,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_242])).

tff(c_248,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_109)
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_247])).

tff(c_67,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_74,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tarski(A_4),k1_zfmisc_1(B_5))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [C_93,A_94,B_95] :
      ( m2_connsp_2(C_93,A_94,B_95)
      | ~ r1_tarski(B_95,k1_tops_1(A_94,C_93))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_269,plain,(
    ! [C_116,A_117,A_118] :
      ( m2_connsp_2(C_116,A_117,k1_tarski(A_118))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(k1_tarski(A_118),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | ~ r2_hidden(A_118,k1_tops_1(A_117,C_116)) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_276,plain,(
    ! [A_118] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_118))
      | ~ m1_subset_1(k1_tarski(A_118),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r2_hidden(A_118,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32,c_269])).

tff(c_282,plain,(
    ! [A_119] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_119))
      | ~ m1_subset_1(k1_tarski(A_119),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_119,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_276])).

tff(c_288,plain,(
    ! [A_120] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_120))
      | ~ r2_hidden(A_120,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_120,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_282])).

tff(c_75,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_89,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_84])).

tff(c_42,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_100,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_65,c_42])).

tff(c_301,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_288,c_100])).

tff(c_302,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_312,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_302])).

tff(c_315,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_312])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_315])).

tff(c_318,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_325,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_248,c_318])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_65,c_325])).

tff(c_333,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_404,plain,(
    ! [C_149,B_150,A_151] :
      ( r2_hidden(C_149,B_150)
      | ~ m1_connsp_2(B_150,A_151,C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_151))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_408,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_404])).

tff(c_412,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_34,c_408])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_333,c_412])).

tff(c_416,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_420,plain,(
    ! [C_154,B_155,A_156] :
      ( ~ v1_xboole_0(C_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(C_154))
      | ~ r2_hidden(A_156,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_426,plain,(
    ! [A_156] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_156,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_420])).

tff(c_427,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_433,plain,(
    ! [A_160,B_161] :
      ( k6_domain_1(A_160,B_161) = k1_tarski(B_161)
      | ~ m1_subset_1(B_161,A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_442,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_433])).

tff(c_447,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_442])).

tff(c_415,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_449,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_415])).

tff(c_522,plain,(
    ! [B_195,A_196,C_197] :
      ( r1_tarski(B_195,k1_tops_1(A_196,C_197))
      | ~ m2_connsp_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_529,plain,(
    ! [B_195] :
      ( r1_tarski(B_195,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_535,plain,(
    ! [B_198] :
      ( r1_tarski(B_198,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_198)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_529])).

tff(c_578,plain,(
    ! [A_204] :
      ( r1_tarski(k1_tarski(A_204),k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_204))
      | ~ r2_hidden(A_204,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | ~ r1_tarski(k1_tarski(A_2),B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_588,plain,(
    ! [A_205] :
      ( r2_hidden(A_205,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_205))
      | ~ r2_hidden(A_205,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_578,c_4])).

tff(c_592,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_449,c_588])).

tff(c_593,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_596,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_593])).

tff(c_599,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_596])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_599])).

tff(c_602,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_16,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_connsp_2(C_19,A_13,B_17)
      | ~ r2_hidden(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_619,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_602,c_16])).

tff(c_624,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_619])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_416,c_624])).

tff(c_628,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_28,plain,(
    ! [A_35,B_36] :
      ( m1_connsp_2('#skF_1'(A_35,B_36),A_35,B_36)
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_677,plain,(
    ! [C_226,A_227,B_228] :
      ( m1_subset_1(C_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_connsp_2(C_226,A_227,B_228)
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_680,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1('#skF_1'(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_28,c_677])).

tff(c_695,plain,(
    ! [C_234,B_235,A_236] :
      ( r2_hidden(C_234,B_235)
      | ~ m1_connsp_2(B_235,A_236,C_234)
      | ~ m1_subset_1(C_234,u1_struct_0(A_236))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_699,plain,(
    ! [B_237,A_238] :
      ( r2_hidden(B_237,'#skF_1'(A_238,B_237))
      | ~ m1_subset_1('#skF_1'(A_238,B_237),k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ m1_subset_1(B_237,u1_struct_0(A_238))
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_28,c_695])).

tff(c_703,plain,(
    ! [B_239,A_240] :
      ( r2_hidden(B_239,'#skF_1'(A_240,B_239))
      | ~ m1_subset_1(B_239,u1_struct_0(A_240))
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_680,c_699])).

tff(c_681,plain,(
    ! [A_229,B_230] :
      ( m1_subset_1('#skF_1'(A_229,B_230),k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_subset_1(B_230,u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_28,c_677])).

tff(c_12,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_688,plain,(
    ! [A_229,A_8,B_230] :
      ( ~ v1_xboole_0(u1_struct_0(A_229))
      | ~ r2_hidden(A_8,'#skF_1'(A_229,B_230))
      | ~ m1_subset_1(B_230,u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_681,c_12])).

tff(c_716,plain,(
    ! [A_244,B_245] :
      ( ~ v1_xboole_0(u1_struct_0(A_244))
      | ~ m1_subset_1(B_245,u1_struct_0(A_244))
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_703,c_688])).

tff(c_719,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_716])).

tff(c_722,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_628,c_719])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.51  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.13/1.51  
% 3.13/1.51  %Foreground sorts:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Background operators:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Foreground operators:
% 3.13/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.51  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.13/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.51  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.13/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.51  
% 3.32/1.53  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.32/1.53  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.32/1.53  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.32/1.53  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.32/1.53  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.32/1.53  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.32/1.53  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.32/1.53  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.32/1.53  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.32/1.53  tff(f_123, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.32/1.53  tff(f_100, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.32/1.53  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_48, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_65, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 3.32/1.53  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_235, plain, (![B_109, A_110, C_111]: (r2_hidden(B_109, k1_tops_1(A_110, C_111)) | ~m1_connsp_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(B_109, u1_struct_0(A_110)) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.53  tff(c_242, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_235])).
% 3.32/1.53  tff(c_247, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_242])).
% 3.32/1.53  tff(c_248, plain, (![B_109]: (r2_hidden(B_109, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_109) | ~m1_subset_1(B_109, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_247])).
% 3.32/1.53  tff(c_67, plain, (![C_58, B_59, A_60]: (~v1_xboole_0(C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.32/1.53  tff(c_73, plain, (![A_60]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_67])).
% 3.32/1.53  tff(c_74, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_73])).
% 3.32/1.53  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.53  tff(c_8, plain, (![A_4, B_5]: (m1_subset_1(k1_tarski(A_4), k1_zfmisc_1(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.53  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.53  tff(c_175, plain, (![C_93, A_94, B_95]: (m2_connsp_2(C_93, A_94, B_95) | ~r1_tarski(B_95, k1_tops_1(A_94, C_93)) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.53  tff(c_269, plain, (![C_116, A_117, A_118]: (m2_connsp_2(C_116, A_117, k1_tarski(A_118)) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(k1_tarski(A_118), k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | ~r2_hidden(A_118, k1_tops_1(A_117, C_116)))), inference(resolution, [status(thm)], [c_6, c_175])).
% 3.32/1.53  tff(c_276, plain, (![A_118]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_118)) | ~m1_subset_1(k1_tarski(A_118), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden(A_118, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_32, c_269])).
% 3.32/1.53  tff(c_282, plain, (![A_119]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_119)) | ~m1_subset_1(k1_tarski(A_119), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_119, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_276])).
% 3.32/1.53  tff(c_288, plain, (![A_120]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_120)) | ~r2_hidden(A_120, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_120, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_282])).
% 3.32/1.53  tff(c_75, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.53  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_75])).
% 3.32/1.53  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_84])).
% 3.32/1.53  tff(c_42, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.32/1.53  tff(c_100, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_65, c_42])).
% 3.32/1.53  tff(c_301, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_288, c_100])).
% 3.32/1.53  tff(c_302, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_301])).
% 3.32/1.53  tff(c_312, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_302])).
% 3.32/1.53  tff(c_315, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_312])).
% 3.32/1.53  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_315])).
% 3.32/1.53  tff(c_318, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_301])).
% 3.32/1.53  tff(c_325, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_248, c_318])).
% 3.32/1.53  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_65, c_325])).
% 3.32/1.53  tff(c_333, plain, (![A_60]: (~r2_hidden(A_60, '#skF_4'))), inference(splitRight, [status(thm)], [c_73])).
% 3.32/1.53  tff(c_404, plain, (![C_149, B_150, A_151]: (r2_hidden(C_149, B_150) | ~m1_connsp_2(B_150, A_151, C_149) | ~m1_subset_1(C_149, u1_struct_0(A_151)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.32/1.53  tff(c_408, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_65, c_404])).
% 3.32/1.53  tff(c_412, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_34, c_408])).
% 3.32/1.53  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_333, c_412])).
% 3.32/1.53  tff(c_416, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.32/1.53  tff(c_420, plain, (![C_154, B_155, A_156]: (~v1_xboole_0(C_154) | ~m1_subset_1(B_155, k1_zfmisc_1(C_154)) | ~r2_hidden(A_156, B_155))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.32/1.53  tff(c_426, plain, (![A_156]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_156, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_420])).
% 3.32/1.53  tff(c_427, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_426])).
% 3.32/1.53  tff(c_433, plain, (![A_160, B_161]: (k6_domain_1(A_160, B_161)=k1_tarski(B_161) | ~m1_subset_1(B_161, A_160) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.53  tff(c_442, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_433])).
% 3.32/1.53  tff(c_447, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_427, c_442])).
% 3.32/1.53  tff(c_415, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 3.32/1.53  tff(c_449, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_415])).
% 3.32/1.53  tff(c_522, plain, (![B_195, A_196, C_197]: (r1_tarski(B_195, k1_tops_1(A_196, C_197)) | ~m2_connsp_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.53  tff(c_529, plain, (![B_195]: (r1_tarski(B_195, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_522])).
% 3.32/1.53  tff(c_535, plain, (![B_198]: (r1_tarski(B_198, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_198) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_529])).
% 3.32/1.53  tff(c_578, plain, (![A_204]: (r1_tarski(k1_tarski(A_204), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_204)) | ~r2_hidden(A_204, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_535])).
% 3.32/1.53  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | ~r1_tarski(k1_tarski(A_2), B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.53  tff(c_588, plain, (![A_205]: (r2_hidden(A_205, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_205)) | ~r2_hidden(A_205, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_578, c_4])).
% 3.32/1.53  tff(c_592, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_449, c_588])).
% 3.32/1.53  tff(c_593, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_592])).
% 3.32/1.53  tff(c_596, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_593])).
% 3.32/1.53  tff(c_599, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_596])).
% 3.32/1.53  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_599])).
% 3.32/1.53  tff(c_602, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_592])).
% 3.32/1.53  tff(c_16, plain, (![C_19, A_13, B_17]: (m1_connsp_2(C_19, A_13, B_17) | ~r2_hidden(B_17, k1_tops_1(A_13, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, u1_struct_0(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.53  tff(c_619, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_602, c_16])).
% 3.32/1.53  tff(c_624, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_619])).
% 3.32/1.53  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_416, c_624])).
% 3.32/1.53  tff(c_628, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_426])).
% 3.32/1.53  tff(c_28, plain, (![A_35, B_36]: (m1_connsp_2('#skF_1'(A_35, B_36), A_35, B_36) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.32/1.53  tff(c_677, plain, (![C_226, A_227, B_228]: (m1_subset_1(C_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_connsp_2(C_226, A_227, B_228) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.53  tff(c_680, plain, (![A_35, B_36]: (m1_subset_1('#skF_1'(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(resolution, [status(thm)], [c_28, c_677])).
% 3.32/1.53  tff(c_695, plain, (![C_234, B_235, A_236]: (r2_hidden(C_234, B_235) | ~m1_connsp_2(B_235, A_236, C_234) | ~m1_subset_1(C_234, u1_struct_0(A_236)) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.32/1.53  tff(c_699, plain, (![B_237, A_238]: (r2_hidden(B_237, '#skF_1'(A_238, B_237)) | ~m1_subset_1('#skF_1'(A_238, B_237), k1_zfmisc_1(u1_struct_0(A_238))) | ~m1_subset_1(B_237, u1_struct_0(A_238)) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_28, c_695])).
% 3.32/1.53  tff(c_703, plain, (![B_239, A_240]: (r2_hidden(B_239, '#skF_1'(A_240, B_239)) | ~m1_subset_1(B_239, u1_struct_0(A_240)) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(resolution, [status(thm)], [c_680, c_699])).
% 3.32/1.53  tff(c_681, plain, (![A_229, B_230]: (m1_subset_1('#skF_1'(A_229, B_230), k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_subset_1(B_230, u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_28, c_677])).
% 3.32/1.53  tff(c_12, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.32/1.53  tff(c_688, plain, (![A_229, A_8, B_230]: (~v1_xboole_0(u1_struct_0(A_229)) | ~r2_hidden(A_8, '#skF_1'(A_229, B_230)) | ~m1_subset_1(B_230, u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_681, c_12])).
% 3.32/1.53  tff(c_716, plain, (![A_244, B_245]: (~v1_xboole_0(u1_struct_0(A_244)) | ~m1_subset_1(B_245, u1_struct_0(A_244)) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_703, c_688])).
% 3.32/1.53  tff(c_719, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_716])).
% 3.32/1.53  tff(c_722, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_628, c_719])).
% 3.32/1.53  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_722])).
% 3.32/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.53  
% 3.32/1.53  Inference rules
% 3.32/1.53  ----------------------
% 3.32/1.53  #Ref     : 0
% 3.32/1.53  #Sup     : 133
% 3.32/1.53  #Fact    : 0
% 3.32/1.53  #Define  : 0
% 3.32/1.53  #Split   : 15
% 3.32/1.53  #Chain   : 0
% 3.32/1.53  #Close   : 0
% 3.32/1.53  
% 3.32/1.53  Ordering : KBO
% 3.32/1.53  
% 3.32/1.53  Simplification rules
% 3.32/1.53  ----------------------
% 3.32/1.53  #Subsume      : 13
% 3.32/1.53  #Demod        : 79
% 3.32/1.53  #Tautology    : 37
% 3.32/1.53  #SimpNegUnit  : 18
% 3.32/1.53  #BackRed      : 1
% 3.32/1.53  
% 3.32/1.53  #Partial instantiations: 0
% 3.32/1.53  #Strategies tried      : 1
% 3.32/1.53  
% 3.32/1.53  Timing (in seconds)
% 3.32/1.53  ----------------------
% 3.32/1.53  Preprocessing        : 0.34
% 3.32/1.53  Parsing              : 0.19
% 3.32/1.53  CNF conversion       : 0.02
% 3.32/1.53  Main loop            : 0.36
% 3.32/1.53  Inferencing          : 0.15
% 3.32/1.53  Reduction            : 0.10
% 3.32/1.53  Demodulation         : 0.06
% 3.32/1.53  BG Simplification    : 0.02
% 3.32/1.53  Subsumption          : 0.06
% 3.32/1.53  Abstraction          : 0.02
% 3.32/1.53  MUC search           : 0.00
% 3.32/1.53  Cooper               : 0.00
% 3.32/1.53  Total                : 0.74
% 3.32/1.53  Index Insertion      : 0.00
% 3.32/1.53  Index Deletion       : 0.00
% 3.32/1.54  Index Matching       : 0.00
% 3.32/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
