%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 179 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 486 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tops_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tops_1(A_39,B_40),B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_41] :
      ( r1_tarski(k1_tops_1(A_41,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_98,plain,(
    ! [A_44] :
      ( k1_tops_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_82,c_52])).

tff(c_102,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_125,plain,(
    ! [B_48,A_49] :
      ( v2_tops_1(B_48,A_49)
      | k1_tops_1(A_49,B_48) != k1_xboole_0
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    ! [A_52] :
      ( v2_tops_1(k1_xboole_0,A_52)
      | k1_tops_1(A_52,k1_xboole_0) != k1_xboole_0
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_112,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(k1_tops_1(A_45,B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v2_tops_1(B_46,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [A_47] :
      ( v1_xboole_0(k1_tops_1(A_47,k1_xboole_0))
      | ~ v2_tops_1(k1_xboole_0,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_121,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v2_tops_1(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_118])).

tff(c_123,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v2_tops_1(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121])).

tff(c_124,plain,(
    ~ v2_tops_1(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_140,plain,
    ( k1_tops_1('#skF_2',k1_xboole_0) != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_137,c_124])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102,c_140])).

tff(c_145,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_154,plain,(
    ! [B_56,A_57] :
      ( v2_tex_2(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ v1_xboole_0(B_56)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_158,plain,(
    ! [A_57] :
      ( v2_tex_2(k1_xboole_0,A_57)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_161,plain,(
    ! [A_57] :
      ( v2_tex_2(k1_xboole_0,A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_158])).

tff(c_174,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1('#skF_1'(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v3_tdlat_3(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [B_26] :
      ( ~ v3_tex_2(B_26,'#skF_2')
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_198,plain,(
    ! [B_64] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_64),'#skF_2')
      | ~ v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_174,c_30])).

tff(c_209,plain,(
    ! [B_64] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_64),'#skF_2')
      | ~ v2_tex_2(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_198])).

tff(c_211,plain,(
    ! [B_65] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_65),'#skF_2')
      | ~ v2_tex_2(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_209])).

tff(c_224,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_211])).

tff(c_225,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_228,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_161,c_225])).

tff(c_231,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_231])).

tff(c_235,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_169,plain,(
    ! [A_61,B_62] :
      ( v3_tex_2('#skF_1'(A_61,B_62),A_61)
      | ~ v2_tex_2(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v3_tdlat_3(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_237,plain,(
    ! [A_67] :
      ( v3_tex_2('#skF_1'(A_67,k1_xboole_0),A_67)
      | ~ v2_tex_2(k1_xboole_0,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_234,plain,(
    ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_240,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_234])).

tff(c_243,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_235,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.27  %$ v3_tex_2 > v2_tops_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.27  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.19/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.27  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.19/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.19/1.27  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.27  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.29  tff(f_117, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.19/1.29  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.19/1.29  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.19/1.29  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.19/1.29  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.19/1.29  tff(f_49, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 2.19/1.29  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.19/1.29  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.19/1.29  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.19/1.29  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.19/1.29  tff(c_34, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.19/1.29  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.19/1.29  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.29  tff(c_77, plain, (![A_39, B_40]: (r1_tarski(k1_tops_1(A_39, B_40), B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.29  tff(c_82, plain, (![A_41]: (r1_tarski(k1_tops_1(A_41, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.19/1.29  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.29  tff(c_43, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.29  tff(c_52, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_43])).
% 2.19/1.29  tff(c_98, plain, (![A_44]: (k1_tops_1(A_44, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_82, c_52])).
% 2.19/1.29  tff(c_102, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.19/1.29  tff(c_125, plain, (![B_48, A_49]: (v2_tops_1(B_48, A_49) | k1_tops_1(A_49, B_48)!=k1_xboole_0 | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.29  tff(c_137, plain, (![A_52]: (v2_tops_1(k1_xboole_0, A_52) | k1_tops_1(A_52, k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_10, c_125])).
% 2.19/1.29  tff(c_112, plain, (![A_45, B_46]: (v1_xboole_0(k1_tops_1(A_45, B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~v2_tops_1(B_46, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.29  tff(c_118, plain, (![A_47]: (v1_xboole_0(k1_tops_1(A_47, k1_xboole_0)) | ~v2_tops_1(k1_xboole_0, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_10, c_112])).
% 2.19/1.29  tff(c_121, plain, (v1_xboole_0(k1_xboole_0) | ~v2_tops_1(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_118])).
% 2.19/1.29  tff(c_123, plain, (v1_xboole_0(k1_xboole_0) | ~v2_tops_1(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121])).
% 2.19/1.29  tff(c_124, plain, (~v2_tops_1(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_123])).
% 2.19/1.29  tff(c_140, plain, (k1_tops_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_137, c_124])).
% 2.19/1.29  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_102, c_140])).
% 2.19/1.29  tff(c_145, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_123])).
% 2.19/1.29  tff(c_154, plain, (![B_56, A_57]: (v2_tex_2(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~v1_xboole_0(B_56) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.29  tff(c_158, plain, (![A_57]: (v2_tex_2(k1_xboole_0, A_57) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.19/1.29  tff(c_161, plain, (![A_57]: (v2_tex_2(k1_xboole_0, A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_158])).
% 2.19/1.29  tff(c_174, plain, (![A_63, B_64]: (m1_subset_1('#skF_1'(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v3_tdlat_3(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.19/1.29  tff(c_30, plain, (![B_26]: (~v3_tex_2(B_26, '#skF_2') | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.19/1.29  tff(c_198, plain, (![B_64]: (~v3_tex_2('#skF_1'('#skF_2', B_64), '#skF_2') | ~v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_174, c_30])).
% 2.19/1.29  tff(c_209, plain, (![B_64]: (~v3_tex_2('#skF_1'('#skF_2', B_64), '#skF_2') | ~v2_tex_2(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_198])).
% 2.19/1.29  tff(c_211, plain, (![B_65]: (~v3_tex_2('#skF_1'('#skF_2', B_65), '#skF_2') | ~v2_tex_2(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_209])).
% 2.19/1.29  tff(c_224, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_10, c_211])).
% 2.19/1.29  tff(c_225, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_224])).
% 2.19/1.29  tff(c_228, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_161, c_225])).
% 2.19/1.29  tff(c_231, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_228])).
% 2.19/1.29  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_231])).
% 2.19/1.29  tff(c_235, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_224])).
% 2.19/1.29  tff(c_169, plain, (![A_61, B_62]: (v3_tex_2('#skF_1'(A_61, B_62), A_61) | ~v2_tex_2(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v3_tdlat_3(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.19/1.29  tff(c_237, plain, (![A_67]: (v3_tex_2('#skF_1'(A_67, k1_xboole_0), A_67) | ~v2_tex_2(k1_xboole_0, A_67) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_10, c_169])).
% 2.19/1.29  tff(c_234, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2')), inference(splitRight, [status(thm)], [c_224])).
% 2.19/1.29  tff(c_240, plain, (~v2_tex_2(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_237, c_234])).
% 2.19/1.29  tff(c_243, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_235, c_240])).
% 2.19/1.29  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_243])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 36
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 2
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 2
% 2.19/1.29  #Demod        : 22
% 2.19/1.29  #Tautology    : 8
% 2.19/1.29  #SimpNegUnit  : 4
% 2.19/1.29  #BackRed      : 0
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.29  Preprocessing        : 0.29
% 2.19/1.29  Parsing              : 0.17
% 2.19/1.29  CNF conversion       : 0.02
% 2.19/1.29  Main loop            : 0.21
% 2.19/1.29  Inferencing          : 0.09
% 2.19/1.29  Reduction            : 0.05
% 2.19/1.29  Demodulation         : 0.04
% 2.19/1.29  BG Simplification    : 0.01
% 2.19/1.29  Subsumption          : 0.04
% 2.19/1.29  Abstraction          : 0.01
% 2.19/1.29  MUC search           : 0.00
% 2.19/1.29  Cooper               : 0.00
% 2.19/1.29  Total                : 0.53
% 2.19/1.29  Index Insertion      : 0.00
% 2.19/1.29  Index Deletion       : 0.00
% 2.19/1.29  Index Matching       : 0.00
% 2.19/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
