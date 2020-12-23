%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 175 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 ( 752 expanded)
%              Number of equality atoms :    4 (   8 expanded)
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

tff(f_105,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_75,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_20,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_122,plain,(
    ! [B_48,A_49,C_50] :
      ( r2_hidden(B_48,k1_tops_1(A_49,C_50))
      | ~ m1_connsp_2(C_50,A_49,B_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_48,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_126,plain,(
    ! [B_48] :
      ( r2_hidden(B_48,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_122])).

tff(c_130,plain,(
    ! [B_48] :
      ( r2_hidden(B_48,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_126])).

tff(c_131,plain,(
    ! [B_48] :
      ( r2_hidden(B_48,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_130])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tops_1(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_43,B_44] :
      ( k1_tops_1(A_43,k1_tops_1(A_43,B_44)) = k1_tops_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_79,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_244,plain,(
    ! [C_59,A_60,B_61] :
      ( m1_connsp_2(C_59,A_60,B_61)
      | ~ r2_hidden(B_61,k1_tops_1(A_60,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_250,plain,(
    ! [B_61] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_61)
      | ~ r2_hidden(B_61,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_244])).

tff(c_259,plain,(
    ! [B_61] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_61)
      | ~ r2_hidden(B_61,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_250])).

tff(c_260,plain,(
    ! [B_61] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_61)
      | ~ r2_hidden(B_61,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_259])).

tff(c_262,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_291,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_291])).

tff(c_338,plain,(
    ! [B_65] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_65)
      | ~ r2_hidden(B_65,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_51,plain,(
    ! [A_39,B_40] :
      ( v3_pre_topc(k1_tops_1(A_39,B_40),A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_56,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_53])).

tff(c_37,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tops_1(A_36,B_37),B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_42,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_39])).

tff(c_57,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tops_1(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [D_32] :
      ( ~ r1_tarski(D_32,'#skF_4')
      | ~ v3_pre_topc(D_32,'#skF_2')
      | ~ m1_connsp_2(D_32,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_63,plain,(
    ! [B_42] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_42),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_42),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_42),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_57,c_18])).

tff(c_105,plain,(
    ! [B_47] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_47),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_47),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_47),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_63])).

tff(c_112,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_118,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42,c_112])).

tff(c_119,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_341,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_338,c_119])).

tff(c_344,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_341])).

tff(c_352,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_131,c_344])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_352])).

tff(c_357,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_361,plain,(
    ! [B_67,A_68,C_69] :
      ( r2_hidden(B_67,k1_tops_1(A_68,C_69))
      | ~ m1_connsp_2(C_69,A_68,B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_67,u1_struct_0(A_68))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_365,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_67)
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_369,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_67)
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_365])).

tff(c_371,plain,(
    ! [B_70] :
      ( r2_hidden(B_70,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_369])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_374,plain,(
    ! [B_70] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_70)
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_371,c_2])).

tff(c_378,plain,(
    ! [B_71] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_71)
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_374])).

tff(c_381,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_378])).

tff(c_385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.31  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.24/1.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.24/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.31  
% 2.24/1.33  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.24/1.33  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.24/1.33  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.24/1.33  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 2.24/1.33  tff(f_45, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.24/1.33  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.24/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.24/1.33  tff(c_20, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_122, plain, (![B_48, A_49, C_50]: (r2_hidden(B_48, k1_tops_1(A_49, C_50)) | ~m1_connsp_2(C_50, A_49, B_48) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_48, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.33  tff(c_126, plain, (![B_48]: (r2_hidden(B_48, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_122])).
% 2.24/1.33  tff(c_130, plain, (![B_48]: (r2_hidden(B_48, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_126])).
% 2.24/1.33  tff(c_131, plain, (![B_48]: (r2_hidden(B_48, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_130])).
% 2.24/1.33  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k1_tops_1(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.33  tff(c_71, plain, (![A_43, B_44]: (k1_tops_1(A_43, k1_tops_1(A_43, B_44))=k1_tops_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.33  tff(c_75, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.24/1.33  tff(c_79, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75])).
% 2.24/1.33  tff(c_244, plain, (![C_59, A_60, B_61]: (m1_connsp_2(C_59, A_60, B_61) | ~r2_hidden(B_61, k1_tops_1(A_60, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.33  tff(c_250, plain, (![B_61]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_61) | ~r2_hidden(B_61, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_61, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_244])).
% 2.24/1.33  tff(c_259, plain, (![B_61]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_61) | ~r2_hidden(B_61, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_61, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_250])).
% 2.24/1.33  tff(c_260, plain, (![B_61]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_61) | ~r2_hidden(B_61, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_61, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_259])).
% 2.24/1.33  tff(c_262, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_260])).
% 2.24/1.33  tff(c_291, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_262])).
% 2.24/1.33  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_291])).
% 2.24/1.33  tff(c_338, plain, (![B_65]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_65) | ~r2_hidden(B_65, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_65, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_260])).
% 2.24/1.33  tff(c_51, plain, (![A_39, B_40]: (v3_pre_topc(k1_tops_1(A_39, B_40), A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.33  tff(c_53, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.24/1.33  tff(c_56, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_53])).
% 2.24/1.33  tff(c_37, plain, (![A_36, B_37]: (r1_tarski(k1_tops_1(A_36, B_37), B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.33  tff(c_39, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.24/1.33  tff(c_42, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_39])).
% 2.24/1.33  tff(c_57, plain, (![A_41, B_42]: (m1_subset_1(k1_tops_1(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.33  tff(c_18, plain, (![D_32]: (~r1_tarski(D_32, '#skF_4') | ~v3_pre_topc(D_32, '#skF_2') | ~m1_connsp_2(D_32, '#skF_2', '#skF_3') | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.24/1.33  tff(c_63, plain, (![B_42]: (~r1_tarski(k1_tops_1('#skF_2', B_42), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_42), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_42), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_57, c_18])).
% 2.24/1.33  tff(c_105, plain, (![B_47]: (~r1_tarski(k1_tops_1('#skF_2', B_47), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_47), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_47), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_63])).
% 2.24/1.33  tff(c_112, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_105])).
% 2.24/1.33  tff(c_118, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_42, c_112])).
% 2.24/1.33  tff(c_119, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_118])).
% 2.24/1.33  tff(c_341, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_338, c_119])).
% 2.24/1.33  tff(c_344, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_341])).
% 2.24/1.33  tff(c_352, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_131, c_344])).
% 2.24/1.33  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_352])).
% 2.24/1.33  tff(c_357, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_118])).
% 2.24/1.33  tff(c_361, plain, (![B_67, A_68, C_69]: (r2_hidden(B_67, k1_tops_1(A_68, C_69)) | ~m1_connsp_2(C_69, A_68, B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_67, u1_struct_0(A_68)) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.33  tff(c_365, plain, (![B_67]: (r2_hidden(B_67, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_67) | ~m1_subset_1(B_67, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_361])).
% 2.24/1.33  tff(c_369, plain, (![B_67]: (r2_hidden(B_67, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_67) | ~m1_subset_1(B_67, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_365])).
% 2.24/1.33  tff(c_371, plain, (![B_70]: (r2_hidden(B_70, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_369])).
% 2.24/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.33  tff(c_374, plain, (![B_70]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_70) | ~m1_subset_1(B_70, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_371, c_2])).
% 2.24/1.33  tff(c_378, plain, (![B_71]: (~m1_connsp_2('#skF_4', '#skF_2', B_71) | ~m1_subset_1(B_71, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_374])).
% 2.24/1.33  tff(c_381, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_378])).
% 2.24/1.33  tff(c_385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_381])).
% 2.24/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  Inference rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Ref     : 0
% 2.24/1.33  #Sup     : 69
% 2.24/1.33  #Fact    : 0
% 2.24/1.33  #Define  : 0
% 2.24/1.33  #Split   : 4
% 2.24/1.33  #Chain   : 0
% 2.24/1.33  #Close   : 0
% 2.24/1.33  
% 2.24/1.33  Ordering : KBO
% 2.24/1.33  
% 2.24/1.33  Simplification rules
% 2.24/1.33  ----------------------
% 2.24/1.33  #Subsume      : 7
% 2.24/1.33  #Demod        : 101
% 2.24/1.33  #Tautology    : 29
% 2.24/1.33  #SimpNegUnit  : 11
% 2.24/1.33  #BackRed      : 0
% 2.24/1.33  
% 2.24/1.33  #Partial instantiations: 0
% 2.24/1.33  #Strategies tried      : 1
% 2.24/1.33  
% 2.24/1.33  Timing (in seconds)
% 2.24/1.33  ----------------------
% 2.64/1.33  Preprocessing        : 0.29
% 2.64/1.33  Parsing              : 0.16
% 2.64/1.33  CNF conversion       : 0.02
% 2.64/1.33  Main loop            : 0.28
% 2.64/1.33  Inferencing          : 0.11
% 2.64/1.33  Reduction            : 0.08
% 2.64/1.33  Demodulation         : 0.06
% 2.64/1.33  BG Simplification    : 0.02
% 2.64/1.33  Subsumption          : 0.06
% 2.64/1.33  Abstraction          : 0.01
% 2.64/1.34  MUC search           : 0.00
% 2.64/1.34  Cooper               : 0.00
% 2.64/1.34  Total                : 0.60
% 2.64/1.34  Index Insertion      : 0.00
% 2.64/1.34  Index Deletion       : 0.00
% 2.64/1.34  Index Matching       : 0.00
% 2.64/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
