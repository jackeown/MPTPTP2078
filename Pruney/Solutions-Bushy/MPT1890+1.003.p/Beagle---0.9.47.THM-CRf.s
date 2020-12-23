%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1890+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:38 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 192 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 818 expanded)
%              Number of equality atoms :   14 (  80 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    ! [A_12,B_20] :
      ( m1_subset_1('#skF_1'(A_12,B_20),u1_struct_0(A_12))
      | v2_tex_2(B_20,A_12)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v3_tdlat_3(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),B_48)
      | v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v3_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_78,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_71])).

tff(c_83,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_78])).

tff(c_84,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_83])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k6_domain_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_45,B_46] :
      ( v4_pre_topc(k2_pre_topc(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ! [A_45,B_4] :
      ( v4_pre_topc(k2_pre_topc(A_45,k6_domain_1(u1_struct_0(A_45),B_4)),A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | ~ m1_subset_1(B_4,u1_struct_0(A_45))
      | v1_xboole_0(u1_struct_0(A_45)) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k2_pre_topc(A_1,B_2),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_22,plain,(
    ! [C_30] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_30))) = k6_domain_1(u1_struct_0('#skF_2'),C_30)
      | ~ r2_hidden(C_30,'#skF_3')
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_99,plain,(
    ! [A_64,B_65,D_66] :
      ( k9_subset_1(u1_struct_0(A_64),B_65,D_66) != k6_domain_1(u1_struct_0(A_64),'#skF_1'(A_64,B_65))
      | ~ v4_pre_topc(D_66,A_64)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v3_tdlat_3(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_101,plain,(
    ! [C_30] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_30) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_30)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_30)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_30,'#skF_3')
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_99])).

tff(c_103,plain,(
    ! [C_30] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_30) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_30)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_30)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_30,'#skF_3')
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_101])).

tff(c_106,plain,(
    ! [C_69] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_69) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_69)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_69)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_69,'#skF_3')
      | ~ m1_subset_1(C_69,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_103])).

tff(c_109,plain,(
    ! [C_69] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_69) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_69)),'#skF_2')
      | ~ r2_hidden(C_69,'#skF_3')
      | ~ m1_subset_1(C_69,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_69),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_113,plain,(
    ! [C_70] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_70) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_70)),'#skF_2')
      | ~ r2_hidden(C_70,'#skF_3')
      | ~ m1_subset_1(C_70,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_70),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_118,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_4)),'#skF_2')
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_120,plain,(
    ! [B_71] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_71) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_71)),'#skF_2')
      | ~ r2_hidden(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_124,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_67,c_120])).

tff(c_127,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_124])).

tff(c_128,plain,(
    ! [B_4] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_4) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_4,'#skF_3')
      | ~ m1_subset_1(B_4,u1_struct_0('#skF_2')) ) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_131,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_128])).

tff(c_133,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_131])).

tff(c_137,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_143,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_137])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_20,c_143])).

tff(c_146,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_10])).

tff(c_152,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_149])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_155])).

tff(c_160,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_163,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_10])).

tff(c_166,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_163])).

tff(c_169,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_169])).

%------------------------------------------------------------------------------
