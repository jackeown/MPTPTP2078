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
% DateTime   : Thu Dec  3 10:30:33 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 139 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 351 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_32,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_5,B_6] : m1_subset_1(k6_subset_1(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_24,B_25] : m1_subset_1(k4_xboole_0(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8])).

tff(c_49,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_75,plain,(
    ! [B_31,A_32] :
      ( v2_tex_2(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_32] :
      ( v2_tex_2(k1_xboole_0,A_32)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_49,c_75])).

tff(c_86,plain,(
    ! [A_32] :
      ( v2_tex_2(k1_xboole_0,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_24,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_115,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1('#skF_1'(A_41,B_42),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ v2_tex_2(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v3_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [B_19] :
      ( ~ v3_tex_2(B_19,'#skF_2')
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_126,plain,(
    ! [B_42] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_42),'#skF_2')
      | ~ v2_tex_2(B_42,'#skF_2')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_115,c_20])).

tff(c_132,plain,(
    ! [B_42] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_42),'#skF_2')
      | ~ v2_tex_2(B_42,'#skF_2')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_126])).

tff(c_134,plain,(
    ! [B_43] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_43),'#skF_2')
      | ~ v2_tex_2(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_132])).

tff(c_151,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_134])).

tff(c_153,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_156,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_153])).

tff(c_159,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_156])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_159])).

tff(c_163,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_29,plain,(
    ! [A_5,B_6] : m1_subset_1(k4_xboole_0(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8])).

tff(c_106,plain,(
    ! [A_39,B_40] :
      ( v3_tex_2('#skF_1'(A_39,B_40),A_39)
      | ~ v2_tex_2(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v3_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    ! [A_39,B_6] :
      ( v3_tex_2('#skF_1'(A_39,k4_xboole_0(u1_struct_0(A_39),B_6)),A_39)
      | ~ v2_tex_2(k4_xboole_0(u1_struct_0(A_39),B_6),A_39)
      | ~ l1_pre_topc(A_39)
      | ~ v3_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_29,c_106])).

tff(c_170,plain,(
    ! [B_46] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',k4_xboole_0(u1_struct_0('#skF_2'),B_46)),'#skF_2')
      | ~ v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'),B_46),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_29,c_134])).

tff(c_174,plain,(
    ! [B_6] :
      ( ~ v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'),B_6),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_170])).

tff(c_181,plain,(
    ! [B_6] :
      ( ~ v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'),B_6),'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_174])).

tff(c_185,plain,(
    ! [B_47] : ~ v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'),B_47),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_181])).

tff(c_192,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_185])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.24  
% 1.94/1.24  %Foreground sorts:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Background operators:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Foreground operators:
% 1.94/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.94/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.24  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.94/1.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.94/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.94/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.24  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.94/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.24  
% 2.10/1.25  tff(f_86, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.10/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.10/1.25  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.10/1.25  tff(f_34, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.25  tff(f_32, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.10/1.25  tff(f_48, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.10/1.25  tff(f_71, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.10/1.25  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.25  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.25  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.10/1.25  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.10/1.25  tff(c_10, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.25  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k6_subset_1(A_5, B_6), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.25  tff(c_46, plain, (![A_24, B_25]: (m1_subset_1(k4_xboole_0(A_24, B_25), k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8])).
% 2.10/1.25  tff(c_49, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_46])).
% 2.10/1.25  tff(c_75, plain, (![B_31, A_32]: (v2_tex_2(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~v1_xboole_0(B_31) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.25  tff(c_79, plain, (![A_32]: (v2_tex_2(k1_xboole_0, A_32) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(resolution, [status(thm)], [c_49, c_75])).
% 2.10/1.25  tff(c_86, plain, (![A_32]: (v2_tex_2(k1_xboole_0, A_32) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_79])).
% 2.10/1.25  tff(c_24, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.25  tff(c_115, plain, (![A_41, B_42]: (m1_subset_1('#skF_1'(A_41, B_42), k1_zfmisc_1(u1_struct_0(A_41))) | ~v2_tex_2(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v3_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.25  tff(c_20, plain, (![B_19]: (~v3_tex_2(B_19, '#skF_2') | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.10/1.25  tff(c_126, plain, (![B_42]: (~v3_tex_2('#skF_1'('#skF_2', B_42), '#skF_2') | ~v2_tex_2(B_42, '#skF_2') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_115, c_20])).
% 2.10/1.25  tff(c_132, plain, (![B_42]: (~v3_tex_2('#skF_1'('#skF_2', B_42), '#skF_2') | ~v2_tex_2(B_42, '#skF_2') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_126])).
% 2.10/1.25  tff(c_134, plain, (![B_43]: (~v3_tex_2('#skF_1'('#skF_2', B_43), '#skF_2') | ~v2_tex_2(B_43, '#skF_2') | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_28, c_132])).
% 2.10/1.25  tff(c_151, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_49, c_134])).
% 2.10/1.25  tff(c_153, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_151])).
% 2.10/1.25  tff(c_156, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_86, c_153])).
% 2.10/1.25  tff(c_159, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_156])).
% 2.10/1.25  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_159])).
% 2.10/1.25  tff(c_163, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_151])).
% 2.10/1.25  tff(c_29, plain, (![A_5, B_6]: (m1_subset_1(k4_xboole_0(A_5, B_6), k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8])).
% 2.10/1.25  tff(c_106, plain, (![A_39, B_40]: (v3_tex_2('#skF_1'(A_39, B_40), A_39) | ~v2_tex_2(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v3_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.25  tff(c_114, plain, (![A_39, B_6]: (v3_tex_2('#skF_1'(A_39, k4_xboole_0(u1_struct_0(A_39), B_6)), A_39) | ~v2_tex_2(k4_xboole_0(u1_struct_0(A_39), B_6), A_39) | ~l1_pre_topc(A_39) | ~v3_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(resolution, [status(thm)], [c_29, c_106])).
% 2.10/1.25  tff(c_170, plain, (![B_46]: (~v3_tex_2('#skF_1'('#skF_2', k4_xboole_0(u1_struct_0('#skF_2'), B_46)), '#skF_2') | ~v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'), B_46), '#skF_2'))), inference(resolution, [status(thm)], [c_29, c_134])).
% 2.10/1.25  tff(c_174, plain, (![B_6]: (~v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'), B_6), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_170])).
% 2.10/1.25  tff(c_181, plain, (![B_6]: (~v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'), B_6), '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_174])).
% 2.10/1.25  tff(c_185, plain, (![B_47]: (~v2_tex_2(k4_xboole_0(u1_struct_0('#skF_2'), B_47), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_181])).
% 2.10/1.25  tff(c_192, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_185])).
% 2.10/1.25  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_192])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 30
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 1
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 4
% 2.10/1.25  #Demod        : 21
% 2.10/1.25  #Tautology    : 6
% 2.10/1.25  #SimpNegUnit  : 5
% 2.10/1.25  #BackRed      : 0
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.26  Preprocessing        : 0.30
% 2.10/1.26  Parsing              : 0.16
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.17
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.05
% 2.18/1.26  Demodulation         : 0.04
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.50
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
