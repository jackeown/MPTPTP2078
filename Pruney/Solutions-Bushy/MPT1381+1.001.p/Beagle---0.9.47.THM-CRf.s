%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1381+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:52 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 129 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 384 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( m1_connsp_2(B,A,C)
                 => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_33,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_43,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_20])).

tff(c_48,plain,(
    ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_22,plain,(
    m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_69,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(k1_tops_1(A_45,B_46),B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    ! [A_45,A_14] :
      ( r1_tarski(k1_tops_1(A_45,A_14),A_14)
      | ~ l1_pre_topc(A_45)
      | ~ r1_tarski(A_14,u1_struct_0(A_45)) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_195,plain,(
    ! [B_89,A_90,C_91] :
      ( r2_hidden(B_89,k1_tops_1(A_90,C_91))
      | ~ m1_connsp_2(C_91,A_90,B_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_89,u1_struct_0(A_90))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_89)
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_195])).

tff(c_204,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_89)
      | ~ m1_subset_1(B_89,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_200])).

tff(c_206,plain,(
    ! [B_92] :
      ( r2_hidden(B_92,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_92)
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_204])).

tff(c_57,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ! [A_38,B_15,A_14] :
      ( m1_subset_1(A_38,B_15)
      | ~ r2_hidden(A_38,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_12,c_57])).

tff(c_249,plain,(
    ! [B_95,B_96] :
      ( m1_subset_1(B_95,B_96)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_96)
      | ~ m1_connsp_2('#skF_2','#skF_1',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_206,c_62])).

tff(c_252,plain,(
    ! [B_95] :
      ( m1_subset_1(B_95,'#skF_2')
      | ~ m1_connsp_2('#skF_2','#skF_1',B_95)
      | ~ m1_subset_1(B_95,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_75,c_249])).

tff(c_269,plain,(
    ! [B_100] :
      ( m1_subset_1(B_100,'#skF_2')
      | ~ m1_connsp_2('#skF_2','#skF_1',B_100)
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28,c_252])).

tff(c_278,plain,
    ( m1_subset_1('#skF_3','#skF_2')
    | ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_269])).

tff(c_283,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_278])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_283])).

tff(c_286,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_308,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k1_tops_1(A_111,B_112),B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_314,plain,(
    ! [A_111,A_14] :
      ( r1_tarski(k1_tops_1(A_111,A_14),A_14)
      | ~ l1_pre_topc(A_111)
      | ~ r1_tarski(A_14,u1_struct_0(A_111)) ) ),
    inference(resolution,[status(thm)],[c_12,c_308])).

tff(c_358,plain,(
    ! [B_134,A_135,C_136] :
      ( r2_hidden(B_134,k1_tops_1(A_135,C_136))
      | ~ m1_connsp_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_134,u1_struct_0(A_135))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_363,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_358])).

tff(c_367,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_363])).

tff(c_369,plain,(
    ! [B_137] :
      ( r2_hidden(B_137,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_connsp_2('#skF_2','#skF_1',B_137)
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_367])).

tff(c_288,plain,(
    ! [C_101,B_102,A_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_293,plain,(
    ! [B_15,A_103,A_14] :
      ( ~ v1_xboole_0(B_15)
      | ~ r2_hidden(A_103,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_12,c_288])).

tff(c_375,plain,(
    ! [B_15,B_137] :
      ( ~ v1_xboole_0(B_15)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_15)
      | ~ m1_connsp_2('#skF_2','#skF_1',B_137)
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_369,c_293])).

tff(c_387,plain,(
    ! [B_140] :
      ( ~ m1_connsp_2('#skF_2','#skF_1',B_140)
      | ~ m1_subset_1(B_140,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_393,plain,(
    ~ m1_connsp_2('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_387])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_393])).

tff(c_400,plain,(
    ! [B_141] :
      ( ~ v1_xboole_0(B_141)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_141) ) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_404,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_314,c_400])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_28,c_286,c_404])).

%------------------------------------------------------------------------------
