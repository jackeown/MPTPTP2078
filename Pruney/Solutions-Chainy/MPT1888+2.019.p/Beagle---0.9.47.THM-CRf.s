%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 495 expanded)
%              Number of leaves         :   31 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          :  182 (1557 expanded)
%              Number of equality atoms :   21 ( 302 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_57,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_63,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_18,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_18])).

tff(c_69,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_66])).

tff(c_72,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_72])).

tff(c_78,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_85,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_58])).

tff(c_77,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_26,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_79,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_26])).

tff(c_112,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_79])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_pre_topc(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    ! [A_70,A_71,B_72] :
      ( m1_subset_1(A_70,u1_struct_0(A_71))
      | ~ r2_hidden(A_70,k2_pre_topc(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_198,plain,(
    ! [A_71,B_72,B_2] :
      ( m1_subset_1('#skF_1'(k2_pre_topc(A_71,B_72),B_2),u1_struct_0(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | r1_xboole_0(k2_pre_topc(A_71,B_72),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_24,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_24])).

tff(c_103,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_80])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [A_59,C_60,B_61] :
      ( k2_pre_topc(A_59,k6_domain_1(u1_struct_0(A_59),C_60)) = k2_pre_topc(A_59,k6_domain_1(u1_struct_0(A_59),B_61))
      | ~ r2_hidden(B_61,k2_pre_topc(A_59,k6_domain_1(u1_struct_0(A_59),C_60)))
      | ~ m1_subset_1(C_60,u1_struct_0(A_59))
      | ~ m1_subset_1(B_61,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59)
      | ~ v3_tdlat_3(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_712,plain,(
    ! [A_147,A_148,C_149] :
      ( k2_pre_topc(A_147,k6_domain_1(u1_struct_0(A_147),'#skF_1'(A_148,k2_pre_topc(A_147,k6_domain_1(u1_struct_0(A_147),C_149))))) = k2_pre_topc(A_147,k6_domain_1(u1_struct_0(A_147),C_149))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1('#skF_1'(A_148,k2_pre_topc(A_147,k6_domain_1(u1_struct_0(A_147),C_149))),u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v3_tdlat_3(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | r1_xboole_0(A_148,k2_pre_topc(A_147,k6_domain_1(u1_struct_0(A_147),C_149))) ) ),
    inference(resolution,[status(thm)],[c_4,c_132])).

tff(c_776,plain,(
    ! [A_148] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_148,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))))) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_148,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_xboole_0(A_148,k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_712])).

tff(c_783,plain,(
    ! [A_148] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_148,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))))) = k2_pre_topc('#skF_2',k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_148,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_xboole_0(A_148,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_36,c_34,c_32,c_77,c_28,c_77,c_776])).

tff(c_1128,plain,(
    ! [A_187] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(A_187,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))))) = k2_pre_topc('#skF_2',k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_187,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2'))
      | r1_xboole_0(A_187,k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_783])).

tff(c_504,plain,(
    ! [A_124,C_125,B_126] :
      ( k2_pre_topc(A_124,k6_domain_1(u1_struct_0(A_124),'#skF_1'(k2_pre_topc(A_124,k6_domain_1(u1_struct_0(A_124),C_125)),B_126))) = k2_pre_topc(A_124,k6_domain_1(u1_struct_0(A_124),C_125))
      | ~ m1_subset_1(C_125,u1_struct_0(A_124))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc(A_124,k6_domain_1(u1_struct_0(A_124),C_125)),B_126),u1_struct_0(A_124))
      | ~ l1_pre_topc(A_124)
      | ~ v3_tdlat_3(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124)
      | r1_xboole_0(k2_pre_topc(A_124,k6_domain_1(u1_struct_0(A_124),C_125)),B_126) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_551,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126))) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_126),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_504])).

tff(c_558,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126))) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_36,c_34,c_32,c_85,c_30,c_85,c_551])).

tff(c_559,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126))) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126),u1_struct_0('#skF_2'))
      | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),B_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_558])).

tff(c_1135,plain,
    ( k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2'))
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2'))
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_559])).

tff(c_1192,plain,
    ( ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_112,c_103,c_1135])).

tff(c_1228,plain,(
    ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_1231,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_198,c_1228])).

tff(c_1237,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1231])).

tff(c_1238,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1237])).

tff(c_1246,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_1238])).

tff(c_1249,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_1246])).

tff(c_1252,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1249])).

tff(c_1254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1252])).

tff(c_1255,plain,(
    ~ m1_subset_1('#skF_1'(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1259,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_198,c_1255])).

tff(c_1265,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1259])).

tff(c_1266,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1265])).

tff(c_1374,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_1266])).

tff(c_1377,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_1374])).

tff(c_1380,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1377])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.71  
% 4.19/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.71  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.19/1.71  
% 4.19/1.71  %Foreground sorts:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Background operators:
% 4.19/1.71  
% 4.19/1.71  
% 4.19/1.71  %Foreground operators:
% 4.19/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.19/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.19/1.71  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.19/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.19/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.19/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.19/1.71  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.19/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.19/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.19/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.19/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.71  
% 4.19/1.74  tff(f_123, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 4.19/1.74  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.19/1.74  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.19/1.74  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.19/1.74  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.19/1.74  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 4.19/1.74  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.19/1.74  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.19/1.74  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.19/1.74  tff(f_103, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 4.19/1.74  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.19/1.74  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_46, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.19/1.74  tff(c_57, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_46])).
% 4.19/1.74  tff(c_63, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_57])).
% 4.19/1.74  tff(c_18, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.19/1.74  tff(c_66, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_63, c_18])).
% 4.19/1.74  tff(c_69, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 4.19/1.74  tff(c_72, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_69])).
% 4.19/1.74  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_72])).
% 4.19/1.74  tff(c_78, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_57])).
% 4.19/1.74  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.19/1.74  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.19/1.74  tff(c_58, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_46])).
% 4.19/1.74  tff(c_85, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_58])).
% 4.19/1.74  tff(c_77, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_57])).
% 4.19/1.74  tff(c_26, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_79, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_26])).
% 4.19/1.74  tff(c_112, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_79])).
% 4.19/1.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.19/1.74  tff(c_104, plain, (![A_51, B_52]: (m1_subset_1(k2_pre_topc(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.19/1.74  tff(c_12, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.19/1.74  tff(c_187, plain, (![A_70, A_71, B_72]: (m1_subset_1(A_70, u1_struct_0(A_71)) | ~r2_hidden(A_70, k2_pre_topc(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_104, c_12])).
% 4.19/1.74  tff(c_198, plain, (![A_71, B_72, B_2]: (m1_subset_1('#skF_1'(k2_pre_topc(A_71, B_72), B_2), u1_struct_0(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | r1_xboole_0(k2_pre_topc(A_71, B_72), B_2))), inference(resolution, [status(thm)], [c_6, c_187])).
% 4.19/1.74  tff(c_24, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_80, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_24])).
% 4.19/1.74  tff(c_103, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_80])).
% 4.19/1.74  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_34, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.19/1.74  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.19/1.74  tff(c_132, plain, (![A_59, C_60, B_61]: (k2_pre_topc(A_59, k6_domain_1(u1_struct_0(A_59), C_60))=k2_pre_topc(A_59, k6_domain_1(u1_struct_0(A_59), B_61)) | ~r2_hidden(B_61, k2_pre_topc(A_59, k6_domain_1(u1_struct_0(A_59), C_60))) | ~m1_subset_1(C_60, u1_struct_0(A_59)) | ~m1_subset_1(B_61, u1_struct_0(A_59)) | ~l1_pre_topc(A_59) | ~v3_tdlat_3(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.19/1.74  tff(c_712, plain, (![A_147, A_148, C_149]: (k2_pre_topc(A_147, k6_domain_1(u1_struct_0(A_147), '#skF_1'(A_148, k2_pre_topc(A_147, k6_domain_1(u1_struct_0(A_147), C_149)))))=k2_pre_topc(A_147, k6_domain_1(u1_struct_0(A_147), C_149)) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1('#skF_1'(A_148, k2_pre_topc(A_147, k6_domain_1(u1_struct_0(A_147), C_149))), u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v3_tdlat_3(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | r1_xboole_0(A_148, k2_pre_topc(A_147, k6_domain_1(u1_struct_0(A_147), C_149))))), inference(resolution, [status(thm)], [c_4, c_132])).
% 4.19/1.74  tff(c_776, plain, (![A_148]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_148, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_148, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_xboole_0(A_148, k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_77, c_712])).
% 4.19/1.74  tff(c_783, plain, (![A_148]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_148, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))))=k2_pre_topc('#skF_2', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_1'(A_148, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_xboole_0(A_148, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_36, c_34, c_32, c_77, c_28, c_77, c_776])).
% 4.19/1.74  tff(c_1128, plain, (![A_187]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(A_187, k2_pre_topc('#skF_2', k1_tarski('#skF_4')))))=k2_pre_topc('#skF_2', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_1'(A_187, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2')) | r1_xboole_0(A_187, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_783])).
% 4.19/1.74  tff(c_504, plain, (![A_124, C_125, B_126]: (k2_pre_topc(A_124, k6_domain_1(u1_struct_0(A_124), '#skF_1'(k2_pre_topc(A_124, k6_domain_1(u1_struct_0(A_124), C_125)), B_126)))=k2_pre_topc(A_124, k6_domain_1(u1_struct_0(A_124), C_125)) | ~m1_subset_1(C_125, u1_struct_0(A_124)) | ~m1_subset_1('#skF_1'(k2_pre_topc(A_124, k6_domain_1(u1_struct_0(A_124), C_125)), B_126), u1_struct_0(A_124)) | ~l1_pre_topc(A_124) | ~v3_tdlat_3(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124) | r1_xboole_0(k2_pre_topc(A_124, k6_domain_1(u1_struct_0(A_124), C_125)), B_126))), inference(resolution, [status(thm)], [c_6, c_132])).
% 4.19/1.74  tff(c_551, plain, (![B_126]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126)))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_126), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), B_126))), inference(superposition, [status(thm), theory('equality')], [c_85, c_504])).
% 4.19/1.74  tff(c_558, plain, (![B_126]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126)))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_36, c_34, c_32, c_85, c_30, c_85, c_551])).
% 4.19/1.74  tff(c_559, plain, (![B_126]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126)))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), B_126))), inference(negUnitSimplification, [status(thm)], [c_38, c_558])).
% 4.19/1.74  tff(c_1135, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2')) | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1128, c_559])).
% 4.19/1.74  tff(c_1192, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_112, c_112, c_103, c_1135])).
% 4.19/1.74  tff(c_1228, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1192])).
% 4.19/1.74  tff(c_1231, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_198, c_1228])).
% 4.19/1.74  tff(c_1237, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1231])).
% 4.19/1.74  tff(c_1238, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_1237])).
% 4.19/1.74  tff(c_1246, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1238])).
% 4.19/1.74  tff(c_1249, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_1246])).
% 4.19/1.74  tff(c_1252, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1249])).
% 4.19/1.74  tff(c_1254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1252])).
% 4.19/1.74  tff(c_1255, plain, (~m1_subset_1('#skF_1'(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1192])).
% 4.19/1.74  tff(c_1259, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_198, c_1255])).
% 4.19/1.74  tff(c_1265, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1259])).
% 4.19/1.74  tff(c_1266, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_112, c_1265])).
% 4.19/1.74  tff(c_1374, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1266])).
% 4.19/1.74  tff(c_1377, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_1374])).
% 4.19/1.74  tff(c_1380, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1377])).
% 4.19/1.74  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1380])).
% 4.19/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.74  
% 4.19/1.74  Inference rules
% 4.19/1.74  ----------------------
% 4.19/1.74  #Ref     : 0
% 4.19/1.74  #Sup     : 292
% 4.19/1.74  #Fact    : 0
% 4.19/1.74  #Define  : 0
% 4.19/1.74  #Split   : 6
% 4.19/1.74  #Chain   : 0
% 4.19/1.74  #Close   : 0
% 4.19/1.74  
% 4.19/1.74  Ordering : KBO
% 4.19/1.74  
% 4.19/1.74  Simplification rules
% 4.19/1.74  ----------------------
% 4.19/1.74  #Subsume      : 0
% 4.19/1.74  #Demod        : 161
% 4.19/1.74  #Tautology    : 34
% 4.19/1.74  #SimpNegUnit  : 52
% 4.19/1.74  #BackRed      : 2
% 4.19/1.74  
% 4.19/1.74  #Partial instantiations: 0
% 4.19/1.74  #Strategies tried      : 1
% 4.19/1.74  
% 4.19/1.74  Timing (in seconds)
% 4.19/1.74  ----------------------
% 4.19/1.74  Preprocessing        : 0.31
% 4.19/1.74  Parsing              : 0.16
% 4.19/1.74  CNF conversion       : 0.02
% 4.19/1.74  Main loop            : 0.65
% 4.19/1.74  Inferencing          : 0.22
% 4.19/1.74  Reduction            : 0.18
% 4.19/1.74  Demodulation         : 0.12
% 4.19/1.74  BG Simplification    : 0.03
% 4.19/1.74  Subsumption          : 0.16
% 4.19/1.74  Abstraction          : 0.04
% 4.19/1.74  MUC search           : 0.00
% 4.19/1.74  Cooper               : 0.00
% 4.19/1.74  Total                : 1.00
% 4.19/1.74  Index Insertion      : 0.00
% 4.19/1.74  Index Deletion       : 0.00
% 4.19/1.74  Index Matching       : 0.00
% 4.19/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
