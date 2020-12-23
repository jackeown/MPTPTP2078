%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:16 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 384 expanded)
%              Number of leaves         :   39 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 (1191 expanded)
%              Number of equality atoms :   16 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_76,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_116,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_62])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_26,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_168,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_183,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_185,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_28,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_188,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_185,c_28])).

tff(c_191,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_188])).

tff(c_194,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_194])).

tff(c_199,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_201,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_76])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_200,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_305,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k6_domain_1(A_98,B_99),k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_322,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_305])).

tff(c_333,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_322])).

tff(c_334,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_333])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1142,plain,(
    ! [B_181,A_182,C_183] :
      ( r2_hidden(B_181,k1_tops_1(A_182,C_183))
      | ~ m1_connsp_2(C_183,A_182,B_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_subset_1(B_181,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1168,plain,(
    ! [B_181] :
      ( r2_hidden(B_181,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_181)
      | ~ m1_subset_1(B_181,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_1142])).

tff(c_1192,plain,(
    ! [B_181] :
      ( r2_hidden(B_181,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_181)
      | ~ m1_subset_1(B_181,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1168])).

tff(c_1202,plain,(
    ! [B_186] :
      ( r2_hidden(B_186,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_186)
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1192])).

tff(c_16,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_206,plain,(
    ! [A_83,C_84,B_85] :
      ( m1_subset_1(A_83,C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_215,plain,(
    ! [A_83,A_12] :
      ( m1_subset_1(A_83,A_12)
      | ~ r2_hidden(A_83,A_12) ) ),
    inference(resolution,[status(thm)],[c_63,c_206])).

tff(c_1212,plain,(
    ! [B_186] :
      ( m1_subset_1(B_186,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_186)
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1202,c_215])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1213,plain,(
    ! [B_186] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_186)
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1202,c_2])).

tff(c_1897,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1213])).

tff(c_1968,plain,(
    ! [B_257] :
      ( m1_subset_1(B_257,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_257)
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1202,c_215])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1971,plain,(
    ! [B_257] :
      ( k6_domain_1(k1_tops_1('#skF_2','#skF_4'),B_257) = k1_tarski(B_257)
      | v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_257)
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1968,c_32])).

tff(c_4181,plain,(
    ! [B_354] :
      ( k6_domain_1(k1_tops_1('#skF_2','#skF_4'),B_354) = k1_tarski(B_354)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_354)
      | ~ m1_subset_1(B_354,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1897,c_1971])).

tff(c_4257,plain,
    ( k6_domain_1(k1_tops_1('#skF_2','#skF_4'),'#skF_3') = k1_tarski('#skF_3')
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_4181])).

tff(c_4296,plain,(
    k6_domain_1(k1_tops_1('#skF_2','#skF_4'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_4257])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_325,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k6_domain_1(A_98,B_99),A_98)
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_305,c_20])).

tff(c_4318,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4296,c_325])).

tff(c_4329,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1897,c_4318])).

tff(c_4332,plain,(
    ~ m1_subset_1('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4329])).

tff(c_4335,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1212,c_4332])).

tff(c_4339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_116,c_4335])).

tff(c_4340,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4329])).

tff(c_38,plain,(
    ! [C_37,A_31,B_35] :
      ( m2_connsp_2(C_37,A_31,B_35)
      | ~ r1_tarski(B_35,k1_tops_1(A_31,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4426,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4340,c_38])).

tff(c_4435,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_334,c_46,c_4426])).

tff(c_4437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_4435])).

tff(c_4440,plain,(
    ! [B_358] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_4475,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_4440])).

tff(c_4494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_4475])).

tff(c_4495,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4599,plain,(
    ! [A_388,B_389] :
      ( k6_domain_1(A_388,B_389) = k1_tarski(B_389)
      | ~ m1_subset_1(B_389,A_388)
      | v1_xboole_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4614,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_4599])).

tff(c_4798,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4614])).

tff(c_4801,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4798,c_28])).

tff(c_4804,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4801])).

tff(c_4807,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_4804])).

tff(c_4811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4807])).

tff(c_4812,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4614])).

tff(c_4521,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_4495,c_62])).

tff(c_4814,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4812,c_4521])).

tff(c_4813,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4614])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k6_domain_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4818,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4812,c_30])).

tff(c_4822,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4818])).

tff(c_4823,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4813,c_4822])).

tff(c_5295,plain,(
    ! [B_469,A_470,C_471] :
      ( r1_tarski(B_469,k1_tops_1(A_470,C_471))
      | ~ m2_connsp_2(C_471,A_470,B_469)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ m1_subset_1(B_469,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5318,plain,(
    ! [B_469] :
      ( r1_tarski(B_469,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_469)
      | ~ m1_subset_1(B_469,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_5295])).

tff(c_5391,plain,(
    ! [B_474] :
      ( r1_tarski(B_474,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_474)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5318])).

tff(c_5408,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4823,c_5391])).

tff(c_5434,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4814,c_5408])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4538,plain,(
    ! [B_369,C_370,A_371] :
      ( r2_hidden(B_369,C_370)
      | ~ r1_tarski(k2_tarski(A_371,B_369),C_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4545,plain,(
    ! [A_5,C_370] :
      ( r2_hidden(A_5,C_370)
      | ~ r1_tarski(k1_tarski(A_5),C_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4538])).

tff(c_5455,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_5434,c_4545])).

tff(c_5474,plain,(
    ! [C_475,A_476,B_477] :
      ( m1_connsp_2(C_475,A_476,B_477)
      | ~ r2_hidden(B_477,k1_tops_1(A_476,C_475))
      | ~ m1_subset_1(C_475,k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ m1_subset_1(B_477,u1_struct_0(A_476))
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5476,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_5455,c_5474])).

tff(c_5482,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_5476])).

tff(c_5484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4495,c_5482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.48/2.66  
% 6.48/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.66  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.66/2.66  
% 6.66/2.66  %Foreground sorts:
% 6.66/2.66  
% 6.66/2.66  
% 6.66/2.66  %Background operators:
% 6.66/2.66  
% 6.66/2.66  
% 6.66/2.66  %Foreground operators:
% 6.66/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.66/2.66  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.66/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.66/2.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.66/2.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.66/2.66  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.66/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.66/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.66/2.66  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.66/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.66/2.66  tff('#skF_2', type, '#skF_2': $i).
% 6.66/2.66  tff('#skF_3', type, '#skF_3': $i).
% 6.66/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.66/2.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.66/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.66  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.66/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.66/2.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.66/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.66/2.66  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 6.66/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.66  
% 6.66/2.68  tff(f_155, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 6.66/2.68  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.66/2.68  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.66/2.68  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.66/2.68  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.66/2.68  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.66/2.68  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.66/2.68  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.66/2.68  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.66/2.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.66/2.68  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.66/2.68  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 6.66/2.68  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.66/2.68  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.66/2.68  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_56, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_76, plain, (~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.66/2.68  tff(c_62, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_116, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_62])).
% 6.66/2.68  tff(c_48, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_26, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.66/2.68  tff(c_168, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.66/2.68  tff(c_183, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_168])).
% 6.66/2.68  tff(c_185, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_183])).
% 6.66/2.68  tff(c_28, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.66/2.68  tff(c_188, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_185, c_28])).
% 6.66/2.68  tff(c_191, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_188])).
% 6.66/2.68  tff(c_194, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_191])).
% 6.66/2.68  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_194])).
% 6.66/2.68  tff(c_199, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_183])).
% 6.66/2.68  tff(c_201, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_76])).
% 6.66/2.68  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_200, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_183])).
% 6.66/2.68  tff(c_305, plain, (![A_98, B_99]: (m1_subset_1(k6_domain_1(A_98, B_99), k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.66/2.68  tff(c_322, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_305])).
% 6.66/2.68  tff(c_333, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_322])).
% 6.66/2.68  tff(c_334, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_200, c_333])).
% 6.66/2.68  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.66/2.68  tff(c_1142, plain, (![B_181, A_182, C_183]: (r2_hidden(B_181, k1_tops_1(A_182, C_183)) | ~m1_connsp_2(C_183, A_182, B_181) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_subset_1(B_181, u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.66/2.68  tff(c_1168, plain, (![B_181]: (r2_hidden(B_181, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_181) | ~m1_subset_1(B_181, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1142])).
% 6.66/2.68  tff(c_1192, plain, (![B_181]: (r2_hidden(B_181, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_181) | ~m1_subset_1(B_181, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1168])).
% 6.66/2.68  tff(c_1202, plain, (![B_186]: (r2_hidden(B_186, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_186) | ~m1_subset_1(B_186, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_1192])).
% 6.66/2.68  tff(c_16, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.66/2.68  tff(c_18, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.66/2.68  tff(c_63, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 6.66/2.68  tff(c_206, plain, (![A_83, C_84, B_85]: (m1_subset_1(A_83, C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.66/2.68  tff(c_215, plain, (![A_83, A_12]: (m1_subset_1(A_83, A_12) | ~r2_hidden(A_83, A_12))), inference(resolution, [status(thm)], [c_63, c_206])).
% 6.66/2.68  tff(c_1212, plain, (![B_186]: (m1_subset_1(B_186, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_186) | ~m1_subset_1(B_186, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1202, c_215])).
% 6.66/2.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.66/2.69  tff(c_1213, plain, (![B_186]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_186) | ~m1_subset_1(B_186, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1202, c_2])).
% 6.66/2.69  tff(c_1897, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1213])).
% 6.66/2.69  tff(c_1968, plain, (![B_257]: (m1_subset_1(B_257, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_257) | ~m1_subset_1(B_257, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1202, c_215])).
% 6.66/2.69  tff(c_32, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.66/2.69  tff(c_1971, plain, (![B_257]: (k6_domain_1(k1_tops_1('#skF_2', '#skF_4'), B_257)=k1_tarski(B_257) | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_257) | ~m1_subset_1(B_257, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1968, c_32])).
% 6.66/2.69  tff(c_4181, plain, (![B_354]: (k6_domain_1(k1_tops_1('#skF_2', '#skF_4'), B_354)=k1_tarski(B_354) | ~m1_connsp_2('#skF_4', '#skF_2', B_354) | ~m1_subset_1(B_354, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1897, c_1971])).
% 6.66/2.69  tff(c_4257, plain, (k6_domain_1(k1_tops_1('#skF_2', '#skF_4'), '#skF_3')=k1_tarski('#skF_3') | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_4181])).
% 6.66/2.69  tff(c_4296, plain, (k6_domain_1(k1_tops_1('#skF_2', '#skF_4'), '#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_4257])).
% 6.66/2.69  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.69  tff(c_325, plain, (![A_98, B_99]: (r1_tarski(k6_domain_1(A_98, B_99), A_98) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_305, c_20])).
% 6.66/2.69  tff(c_4318, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4296, c_325])).
% 6.66/2.69  tff(c_4329, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1897, c_4318])).
% 6.66/2.69  tff(c_4332, plain, (~m1_subset_1('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4329])).
% 6.66/2.69  tff(c_4335, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1212, c_4332])).
% 6.66/2.69  tff(c_4339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_116, c_4335])).
% 6.66/2.69  tff(c_4340, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_4329])).
% 6.66/2.69  tff(c_38, plain, (![C_37, A_31, B_35]: (m2_connsp_2(C_37, A_31, B_35) | ~r1_tarski(B_35, k1_tops_1(A_31, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.66/2.69  tff(c_4426, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4340, c_38])).
% 6.66/2.69  tff(c_4435, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_334, c_46, c_4426])).
% 6.66/2.69  tff(c_4437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_4435])).
% 6.66/2.69  tff(c_4440, plain, (![B_358]: (~m1_connsp_2('#skF_4', '#skF_2', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1213])).
% 6.66/2.69  tff(c_4475, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_4440])).
% 6.66/2.69  tff(c_4494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_4475])).
% 6.66/2.69  tff(c_4495, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 6.66/2.69  tff(c_4599, plain, (![A_388, B_389]: (k6_domain_1(A_388, B_389)=k1_tarski(B_389) | ~m1_subset_1(B_389, A_388) | v1_xboole_0(A_388))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.66/2.69  tff(c_4614, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_4599])).
% 6.66/2.69  tff(c_4798, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4614])).
% 6.66/2.69  tff(c_4801, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4798, c_28])).
% 6.66/2.69  tff(c_4804, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_4801])).
% 6.66/2.69  tff(c_4807, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_4804])).
% 6.66/2.69  tff(c_4811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_4807])).
% 6.66/2.69  tff(c_4812, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_4614])).
% 6.66/2.69  tff(c_4521, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_4495, c_62])).
% 6.66/2.69  tff(c_4814, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4812, c_4521])).
% 6.66/2.69  tff(c_4813, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_4614])).
% 6.66/2.69  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k6_domain_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.66/2.69  tff(c_4818, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4812, c_30])).
% 6.66/2.69  tff(c_4822, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4818])).
% 6.66/2.69  tff(c_4823, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_4813, c_4822])).
% 6.66/2.69  tff(c_5295, plain, (![B_469, A_470, C_471]: (r1_tarski(B_469, k1_tops_1(A_470, C_471)) | ~m2_connsp_2(C_471, A_470, B_469) | ~m1_subset_1(C_471, k1_zfmisc_1(u1_struct_0(A_470))) | ~m1_subset_1(B_469, k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.66/2.69  tff(c_5318, plain, (![B_469]: (r1_tarski(B_469, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_469) | ~m1_subset_1(B_469, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_5295])).
% 6.66/2.69  tff(c_5391, plain, (![B_474]: (r1_tarski(B_474, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_474) | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5318])).
% 6.66/2.69  tff(c_5408, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_4823, c_5391])).
% 6.66/2.69  tff(c_5434, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4814, c_5408])).
% 6.66/2.69  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.66/2.69  tff(c_4538, plain, (![B_369, C_370, A_371]: (r2_hidden(B_369, C_370) | ~r1_tarski(k2_tarski(A_371, B_369), C_370))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.66/2.69  tff(c_4545, plain, (![A_5, C_370]: (r2_hidden(A_5, C_370) | ~r1_tarski(k1_tarski(A_5), C_370))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4538])).
% 6.66/2.69  tff(c_5455, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_5434, c_4545])).
% 6.66/2.69  tff(c_5474, plain, (![C_475, A_476, B_477]: (m1_connsp_2(C_475, A_476, B_477) | ~r2_hidden(B_477, k1_tops_1(A_476, C_475)) | ~m1_subset_1(C_475, k1_zfmisc_1(u1_struct_0(A_476))) | ~m1_subset_1(B_477, u1_struct_0(A_476)) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.66/2.69  tff(c_5476, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_5455, c_5474])).
% 6.66/2.69  tff(c_5482, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_5476])).
% 6.66/2.69  tff(c_5484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_4495, c_5482])).
% 6.66/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.69  
% 6.66/2.69  Inference rules
% 6.66/2.69  ----------------------
% 6.66/2.69  #Ref     : 0
% 6.66/2.69  #Sup     : 1122
% 6.66/2.69  #Fact    : 0
% 6.66/2.69  #Define  : 0
% 6.66/2.69  #Split   : 15
% 6.66/2.69  #Chain   : 0
% 6.66/2.69  #Close   : 0
% 6.66/2.69  
% 6.66/2.69  Ordering : KBO
% 6.66/2.69  
% 6.66/2.69  Simplification rules
% 6.66/2.69  ----------------------
% 6.66/2.69  #Subsume      : 92
% 6.66/2.69  #Demod        : 450
% 6.66/2.69  #Tautology    : 387
% 6.66/2.69  #SimpNegUnit  : 257
% 6.66/2.69  #BackRed      : 2
% 6.66/2.69  
% 6.66/2.69  #Partial instantiations: 0
% 6.66/2.69  #Strategies tried      : 1
% 6.66/2.69  
% 6.66/2.69  Timing (in seconds)
% 6.66/2.69  ----------------------
% 6.66/2.69  Preprocessing        : 0.41
% 6.66/2.69  Parsing              : 0.21
% 6.66/2.69  CNF conversion       : 0.03
% 6.66/2.69  Main loop            : 1.35
% 6.66/2.69  Inferencing          : 0.45
% 6.66/2.69  Reduction            : 0.48
% 6.66/2.69  Demodulation         : 0.34
% 6.66/2.69  BG Simplification    : 0.05
% 6.66/2.69  Subsumption          : 0.28
% 6.66/2.69  Abstraction          : 0.06
% 6.66/2.69  MUC search           : 0.00
% 6.66/2.69  Cooper               : 0.00
% 6.66/2.69  Total                : 1.80
% 6.66/2.69  Index Insertion      : 0.00
% 6.66/2.69  Index Deletion       : 0.00
% 6.66/2.69  Index Matching       : 0.00
% 6.66/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
