%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 427 expanded)
%              Number of leaves         :   28 ( 163 expanded)
%              Depth                    :   26
%              Number of atoms          :  278 (1814 expanded)
%              Number of equality atoms :   12 ( 105 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_45,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_pre_topc(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_45,A_46,B_47] :
      ( m1_subset_1(A_45,u1_struct_0(A_46))
      | ~ r2_hidden(A_45,k2_pre_topc(A_46,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_45,c_8])).

tff(c_67,plain,(
    ! [A_46,B_47,B_2] :
      ( m1_subset_1('#skF_1'(k2_pre_topc(A_46,B_47),B_2),u1_struct_0(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | r1_xboole_0(k2_pre_topc(A_46,B_47),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_74,plain,(
    ! [A_51,C_52,B_53] :
      ( k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52)) = k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),B_53))
      | ~ r2_hidden(B_53,k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52)))
      | ~ m1_subset_1(C_52,u1_struct_0(A_51))
      | ~ m1_subset_1(B_53,u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v3_tdlat_3(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_212,plain,(
    ! [A_115,A_116,C_117] :
      ( k2_pre_topc(A_115,k6_domain_1(u1_struct_0(A_115),'#skF_1'(A_116,k2_pre_topc(A_115,k6_domain_1(u1_struct_0(A_115),C_117))))) = k2_pre_topc(A_115,k6_domain_1(u1_struct_0(A_115),C_117))
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ m1_subset_1('#skF_1'(A_116,k2_pre_topc(A_115,k6_domain_1(u1_struct_0(A_115),C_117))),u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v3_tdlat_3(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | r1_xboole_0(A_116,k2_pre_topc(A_115,k6_domain_1(u1_struct_0(A_115),C_117))) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_290,plain,(
    ! [A_153,C_154,A_155] :
      ( m1_subset_1(k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154)),k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_153),'#skF_1'(A_155,k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154)))),k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ m1_subset_1(C_154,u1_struct_0(A_153))
      | ~ m1_subset_1('#skF_1'(A_155,k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154))),u1_struct_0(A_153))
      | ~ l1_pre_topc(A_153)
      | ~ v3_tdlat_3(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153)
      | r1_xboole_0(A_155,k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_10])).

tff(c_301,plain,(
    ! [A_156,C_157,A_158] :
      ( m1_subset_1(k2_pre_topc(A_156,k6_domain_1(u1_struct_0(A_156),C_157)),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(C_157,u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v3_tdlat_3(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | r1_xboole_0(A_158,k2_pre_topc(A_156,k6_domain_1(u1_struct_0(A_156),C_157)))
      | ~ m1_subset_1('#skF_1'(A_158,k2_pre_topc(A_156,k6_domain_1(u1_struct_0(A_156),C_157))),u1_struct_0(A_156))
      | v1_xboole_0(u1_struct_0(A_156)) ) ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_364,plain,(
    ! [A_162,C_163,B_164] :
      ( m1_subset_1(k2_pre_topc(A_162,k6_domain_1(u1_struct_0(A_162),C_163)),k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ m1_subset_1(C_163,u1_struct_0(A_162))
      | ~ v3_tdlat_3(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162)
      | v1_xboole_0(u1_struct_0(A_162))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | r1_xboole_0(k2_pre_topc(A_162,B_164),k2_pre_topc(A_162,k6_domain_1(u1_struct_0(A_162),C_163))) ) ),
    inference(resolution,[status(thm)],[c_67,c_301])).

tff(c_369,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_364,c_22])).

tff(c_393,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_24,c_369])).

tff(c_394,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_393])).

tff(c_396,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_399,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_396])).

tff(c_402,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_399])).

tff(c_14,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_405,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_402,c_14])).

tff(c_408,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_405])).

tff(c_411,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_411])).

tff(c_417,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_421,plain,(
    ! [A_165] :
      ( m1_subset_1(A_165,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_165,k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_417,c_8])).

tff(c_461,plain,(
    ! [B_172] :
      ( m1_subset_1('#skF_1'(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),B_172),u1_struct_0('#skF_2'))
      | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),B_172) ) ),
    inference(resolution,[status(thm)],[c_6,c_421])).

tff(c_300,plain,(
    ! [A_153,C_154,A_155] :
      ( m1_subset_1(k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154)),k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(C_154,u1_struct_0(A_153))
      | ~ l1_pre_topc(A_153)
      | ~ v3_tdlat_3(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153)
      | r1_xboole_0(A_155,k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154)))
      | ~ m1_subset_1('#skF_1'(A_155,k2_pre_topc(A_153,k6_domain_1(u1_struct_0(A_153),C_154))),u1_struct_0(A_153))
      | v1_xboole_0(u1_struct_0(A_153)) ) ),
    inference(resolution,[status(thm)],[c_16,c_290])).

tff(c_465,plain,(
    ! [C_154] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154))) ) ),
    inference(resolution,[status(thm)],[c_461,c_300])).

tff(c_468,plain,(
    ! [C_154] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_465])).

tff(c_469,plain,(
    ! [C_154] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_468])).

tff(c_470,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_473,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_470,c_14])).

tff(c_476,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_473])).

tff(c_479,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_476])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_479])).

tff(c_485,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_416,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_432,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_449,plain,(
    ! [A_170] :
      ( m1_subset_1(A_170,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_170,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_432,c_8])).

tff(c_486,plain,(
    ! [B_173] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),B_173),u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_449])).

tff(c_490,plain,(
    ! [C_154] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154))) ) ),
    inference(resolution,[status(thm)],[c_486,c_300])).

tff(c_493,plain,(
    ! [C_154] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_154))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_490])).

tff(c_534,plain,(
    ! [C_180] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_180)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_180))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_485,c_34,c_493])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_605,plain,(
    ! [C_185,C_186] :
      ( ~ r2_hidden(C_185,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_186)))
      | ~ r2_hidden(C_185,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')))
      | m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_186)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_186,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_534,c_2])).

tff(c_684,plain,(
    ! [C_192,B_193] :
      ( ~ r2_hidden('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_192)),B_193),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')))
      | m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_192)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_192)),B_193) ) ),
    inference(resolution,[status(thm)],[c_6,c_605])).

tff(c_724,plain,(
    ! [C_198] :
      ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_198)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_198)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_684])).

tff(c_727,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_724,c_22])).

tff(c_740,plain,(
    m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_727])).

tff(c_751,plain,(
    ! [A_199] :
      ( m1_subset_1(A_199,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_199,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_740,c_8])).

tff(c_760,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_2),u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_751])).

tff(c_459,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | r1_xboole_0(A_1,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_449])).

tff(c_83,plain,(
    ! [A_51,C_52,B_2] :
      ( k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),'#skF_1'(k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52)),B_2))) = k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52))
      | ~ m1_subset_1(C_52,u1_struct_0(A_51))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52)),B_2),u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v3_tdlat_3(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | r1_xboole_0(k2_pre_topc(A_51,k6_domain_1(u1_struct_0(A_51),C_52)),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_1099,plain,(
    ! [A_230,C_232,C_231] :
      ( k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_232)) = k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_231))
      | ~ m1_subset_1(C_231,u1_struct_0(A_230))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_231)),k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_232))),u1_struct_0(A_230))
      | ~ l1_pre_topc(A_230)
      | ~ v3_tdlat_3(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | r1_xboole_0(k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_231)),k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_232)))
      | ~ m1_subset_1(C_232,u1_struct_0(A_230))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_231)),k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_232))),u1_struct_0(A_230))
      | ~ l1_pre_topc(A_230)
      | ~ v3_tdlat_3(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | r1_xboole_0(k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_231)),k2_pre_topc(A_230,k6_domain_1(u1_struct_0(A_230),C_232))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_83])).

tff(c_1108,plain,(
    ! [C_231] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1(C_231,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_459,c_1099])).

tff(c_1136,plain,(
    ! [C_231] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1(C_231,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_231)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_24,c_1108])).

tff(c_1194,plain,(
    ! [C_242] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_242)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1(C_242,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_242)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_242)),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1136])).

tff(c_1198,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(resolution,[status(thm)],[c_760,c_1194])).

tff(c_1222,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
    | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1198])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_1222])).

tff(c_1225,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_1229,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1225,c_14])).

tff(c_1232,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1229])).

tff(c_1235,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1232])).

tff(c_1239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.89  
% 4.60/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.89  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.60/1.89  
% 4.60/1.89  %Foreground sorts:
% 4.60/1.89  
% 4.60/1.89  
% 4.60/1.89  %Background operators:
% 4.60/1.89  
% 4.60/1.89  
% 4.60/1.89  %Foreground operators:
% 4.60/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.89  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.60/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.60/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.89  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.60/1.89  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.60/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.60/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.89  
% 4.89/1.91  tff(f_113, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 4.89/1.91  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.89/1.91  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.89/1.91  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.89/1.91  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.89/1.91  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.89/1.91  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 4.89/1.91  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.89/1.91  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.89/1.91  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_22, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_20, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.91  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.91  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_30, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.89/1.91  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/1.91  tff(c_45, plain, (![A_40, B_41]: (m1_subset_1(k2_pre_topc(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.91  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.89/1.91  tff(c_60, plain, (![A_45, A_46, B_47]: (m1_subset_1(A_45, u1_struct_0(A_46)) | ~r2_hidden(A_45, k2_pre_topc(A_46, B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_45, c_8])).
% 4.89/1.91  tff(c_67, plain, (![A_46, B_47, B_2]: (m1_subset_1('#skF_1'(k2_pre_topc(A_46, B_47), B_2), u1_struct_0(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | r1_xboole_0(k2_pre_topc(A_46, B_47), B_2))), inference(resolution, [status(thm)], [c_6, c_60])).
% 4.89/1.91  tff(c_74, plain, (![A_51, C_52, B_53]: (k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52))=k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), B_53)) | ~r2_hidden(B_53, k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52))) | ~m1_subset_1(C_52, u1_struct_0(A_51)) | ~m1_subset_1(B_53, u1_struct_0(A_51)) | ~l1_pre_topc(A_51) | ~v3_tdlat_3(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.89/1.91  tff(c_212, plain, (![A_115, A_116, C_117]: (k2_pre_topc(A_115, k6_domain_1(u1_struct_0(A_115), '#skF_1'(A_116, k2_pre_topc(A_115, k6_domain_1(u1_struct_0(A_115), C_117)))))=k2_pre_topc(A_115, k6_domain_1(u1_struct_0(A_115), C_117)) | ~m1_subset_1(C_117, u1_struct_0(A_115)) | ~m1_subset_1('#skF_1'(A_116, k2_pre_topc(A_115, k6_domain_1(u1_struct_0(A_115), C_117))), u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | ~v3_tdlat_3(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | r1_xboole_0(A_116, k2_pre_topc(A_115, k6_domain_1(u1_struct_0(A_115), C_117))))), inference(resolution, [status(thm)], [c_4, c_74])).
% 4.89/1.91  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.89/1.91  tff(c_290, plain, (![A_153, C_154, A_155]: (m1_subset_1(k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154)), k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_153), '#skF_1'(A_155, k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154)))), k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~m1_subset_1(C_154, u1_struct_0(A_153)) | ~m1_subset_1('#skF_1'(A_155, k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154))), u1_struct_0(A_153)) | ~l1_pre_topc(A_153) | ~v3_tdlat_3(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153) | r1_xboole_0(A_155, k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154))))), inference(superposition, [status(thm), theory('equality')], [c_212, c_10])).
% 4.89/1.91  tff(c_301, plain, (![A_156, C_157, A_158]: (m1_subset_1(k2_pre_topc(A_156, k6_domain_1(u1_struct_0(A_156), C_157)), k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(C_157, u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v3_tdlat_3(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | r1_xboole_0(A_158, k2_pre_topc(A_156, k6_domain_1(u1_struct_0(A_156), C_157))) | ~m1_subset_1('#skF_1'(A_158, k2_pre_topc(A_156, k6_domain_1(u1_struct_0(A_156), C_157))), u1_struct_0(A_156)) | v1_xboole_0(u1_struct_0(A_156)))), inference(resolution, [status(thm)], [c_16, c_290])).
% 4.89/1.91  tff(c_364, plain, (![A_162, C_163, B_164]: (m1_subset_1(k2_pre_topc(A_162, k6_domain_1(u1_struct_0(A_162), C_163)), k1_zfmisc_1(u1_struct_0(A_162))) | ~m1_subset_1(C_163, u1_struct_0(A_162)) | ~v3_tdlat_3(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162) | v1_xboole_0(u1_struct_0(A_162)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | r1_xboole_0(k2_pre_topc(A_162, B_164), k2_pre_topc(A_162, k6_domain_1(u1_struct_0(A_162), C_163))))), inference(resolution, [status(thm)], [c_67, c_301])).
% 4.89/1.91  tff(c_369, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_364, c_22])).
% 4.89/1.91  tff(c_393, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_24, c_369])).
% 4.89/1.91  tff(c_394, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_393])).
% 4.89/1.91  tff(c_396, plain, (~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_394])).
% 4.89/1.91  tff(c_399, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_396])).
% 4.89/1.91  tff(c_402, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_399])).
% 4.89/1.91  tff(c_14, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.89/1.91  tff(c_405, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_402, c_14])).
% 4.89/1.91  tff(c_408, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_405])).
% 4.89/1.91  tff(c_411, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_408])).
% 4.89/1.91  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_411])).
% 4.89/1.91  tff(c_417, plain, (m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_394])).
% 4.89/1.91  tff(c_421, plain, (![A_165]: (m1_subset_1(A_165, u1_struct_0('#skF_2')) | ~r2_hidden(A_165, k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_417, c_8])).
% 4.89/1.91  tff(c_461, plain, (![B_172]: (m1_subset_1('#skF_1'(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), B_172), u1_struct_0('#skF_2')) | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), B_172))), inference(resolution, [status(thm)], [c_6, c_421])).
% 4.89/1.91  tff(c_300, plain, (![A_153, C_154, A_155]: (m1_subset_1(k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154)), k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(C_154, u1_struct_0(A_153)) | ~l1_pre_topc(A_153) | ~v3_tdlat_3(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153) | r1_xboole_0(A_155, k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154))) | ~m1_subset_1('#skF_1'(A_155, k2_pre_topc(A_153, k6_domain_1(u1_struct_0(A_153), C_154))), u1_struct_0(A_153)) | v1_xboole_0(u1_struct_0(A_153)))), inference(resolution, [status(thm)], [c_16, c_290])).
% 4.89/1.91  tff(c_465, plain, (![C_154]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154))))), inference(resolution, [status(thm)], [c_461, c_300])).
% 4.89/1.91  tff(c_468, plain, (![C_154]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_465])).
% 4.89/1.91  tff(c_469, plain, (![C_154]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | r1_xboole_0(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154))))), inference(negUnitSimplification, [status(thm)], [c_34, c_468])).
% 4.89/1.91  tff(c_470, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_469])).
% 4.89/1.91  tff(c_473, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_470, c_14])).
% 4.89/1.91  tff(c_476, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_473])).
% 4.89/1.91  tff(c_479, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_476])).
% 4.89/1.91  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_479])).
% 4.89/1.91  tff(c_485, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_469])).
% 4.89/1.91  tff(c_416, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_394])).
% 4.89/1.91  tff(c_432, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_416])).
% 4.89/1.91  tff(c_449, plain, (![A_170]: (m1_subset_1(A_170, u1_struct_0('#skF_2')) | ~r2_hidden(A_170, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(resolution, [status(thm)], [c_432, c_8])).
% 4.89/1.91  tff(c_486, plain, (![B_173]: (m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), B_173), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), B_173))), inference(resolution, [status(thm)], [c_6, c_449])).
% 4.89/1.91  tff(c_490, plain, (![C_154]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154))))), inference(resolution, [status(thm)], [c_486, c_300])).
% 4.89/1.91  tff(c_493, plain, (![C_154]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_154, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_154))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_490])).
% 4.89/1.91  tff(c_534, plain, (![C_180]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_180)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_180, u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_180))))), inference(negUnitSimplification, [status(thm)], [c_485, c_34, c_493])).
% 4.89/1.91  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.89/1.91  tff(c_605, plain, (![C_185, C_186]: (~r2_hidden(C_185, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_186))) | ~r2_hidden(C_185, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))) | m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_186)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_186, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_534, c_2])).
% 4.89/1.91  tff(c_684, plain, (![C_192, B_193]: (~r2_hidden('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_192)), B_193), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))) | m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_192)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_192)), B_193))), inference(resolution, [status(thm)], [c_6, c_605])).
% 4.89/1.91  tff(c_724, plain, (![C_198]: (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_198)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_198)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(resolution, [status(thm)], [c_4, c_684])).
% 4.89/1.91  tff(c_727, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_724, c_22])).
% 4.89/1.91  tff(c_740, plain, (m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_727])).
% 4.89/1.91  tff(c_751, plain, (![A_199]: (m1_subset_1(A_199, u1_struct_0('#skF_2')) | ~r2_hidden(A_199, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))))), inference(resolution, [status(thm)], [c_740, c_8])).
% 4.89/1.91  tff(c_760, plain, (![B_2]: (m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_2), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_2))), inference(resolution, [status(thm)], [c_6, c_751])).
% 4.89/1.91  tff(c_459, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | r1_xboole_0(A_1, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(resolution, [status(thm)], [c_4, c_449])).
% 4.89/1.91  tff(c_83, plain, (![A_51, C_52, B_2]: (k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), '#skF_1'(k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52)), B_2)))=k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52)) | ~m1_subset_1(C_52, u1_struct_0(A_51)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52)), B_2), u1_struct_0(A_51)) | ~l1_pre_topc(A_51) | ~v3_tdlat_3(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | r1_xboole_0(k2_pre_topc(A_51, k6_domain_1(u1_struct_0(A_51), C_52)), B_2))), inference(resolution, [status(thm)], [c_6, c_74])).
% 4.89/1.91  tff(c_1099, plain, (![A_230, C_232, C_231]: (k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_232))=k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_231)) | ~m1_subset_1(C_231, u1_struct_0(A_230)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_231)), k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_232))), u1_struct_0(A_230)) | ~l1_pre_topc(A_230) | ~v3_tdlat_3(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | r1_xboole_0(k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_231)), k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_232))) | ~m1_subset_1(C_232, u1_struct_0(A_230)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_231)), k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_232))), u1_struct_0(A_230)) | ~l1_pre_topc(A_230) | ~v3_tdlat_3(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | r1_xboole_0(k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_231)), k2_pre_topc(A_230, k6_domain_1(u1_struct_0(A_230), C_232))))), inference(superposition, [status(thm), theory('equality')], [c_212, c_83])).
% 4.89/1.91  tff(c_1108, plain, (![C_231]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(C_231, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(resolution, [status(thm)], [c_459, c_1099])).
% 4.89/1.91  tff(c_1136, plain, (![C_231]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(C_231, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_231)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_24, c_1108])).
% 4.89/1.91  tff(c_1194, plain, (![C_242]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_242))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(C_242, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_242)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_242)), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_1136])).
% 4.89/1.91  tff(c_1198, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(resolution, [status(thm)], [c_760, c_1194])).
% 4.89/1.91  tff(c_1222, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1198])).
% 4.89/1.91  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_1222])).
% 4.89/1.91  tff(c_1225, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_416])).
% 4.89/1.91  tff(c_1229, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1225, c_14])).
% 4.89/1.91  tff(c_1232, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_1229])).
% 4.89/1.91  tff(c_1235, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1232])).
% 4.89/1.91  tff(c_1239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1235])).
% 4.89/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.91  
% 4.89/1.91  Inference rules
% 4.89/1.91  ----------------------
% 4.89/1.91  #Ref     : 0
% 4.89/1.91  #Sup     : 232
% 4.89/1.91  #Fact    : 0
% 4.89/1.91  #Define  : 0
% 4.89/1.91  #Split   : 3
% 4.89/1.91  #Chain   : 0
% 4.89/1.91  #Close   : 0
% 4.89/1.91  
% 4.89/1.91  Ordering : KBO
% 4.89/1.91  
% 4.89/1.91  Simplification rules
% 4.89/1.91  ----------------------
% 4.89/1.91  #Subsume      : 15
% 4.89/1.91  #Demod        : 213
% 4.89/1.91  #Tautology    : 15
% 4.89/1.91  #SimpNegUnit  : 64
% 4.89/1.91  #BackRed      : 0
% 4.89/1.91  
% 4.89/1.91  #Partial instantiations: 0
% 4.89/1.91  #Strategies tried      : 1
% 4.89/1.91  
% 4.89/1.91  Timing (in seconds)
% 4.89/1.91  ----------------------
% 4.89/1.92  Preprocessing        : 0.34
% 4.89/1.92  Parsing              : 0.18
% 4.89/1.92  CNF conversion       : 0.02
% 4.89/1.92  Main loop            : 0.75
% 4.89/1.92  Inferencing          : 0.28
% 4.89/1.92  Reduction            : 0.19
% 4.89/1.92  Demodulation         : 0.13
% 4.89/1.92  BG Simplification    : 0.03
% 4.89/1.92  Subsumption          : 0.21
% 4.89/1.92  Abstraction          : 0.04
% 4.89/1.92  MUC search           : 0.00
% 4.89/1.92  Cooper               : 0.00
% 4.89/1.92  Total                : 1.13
% 4.89/1.92  Index Insertion      : 0.00
% 4.89/1.92  Index Deletion       : 0.00
% 4.89/1.92  Index Matching       : 0.00
% 4.89/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
