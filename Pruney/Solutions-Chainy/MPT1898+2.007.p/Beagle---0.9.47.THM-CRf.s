%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 163 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 414 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tops_1 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_98,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tops_1(A_36,B_37),B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_40,A_41] :
      ( r1_tarski(k1_tops_1(A_40,A_41),A_41)
      | ~ l1_pre_topc(A_40)
      | ~ r1_tarski(A_41,u1_struct_0(A_40)) ) ),
    inference(resolution,[status(thm)],[c_12,c_88])).

tff(c_65,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_103,plain,(
    ! [A_40] :
      ( k1_tops_1(A_40,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_40)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_40)) ) ),
    inference(resolution,[status(thm)],[c_99,c_74])).

tff(c_115,plain,(
    ! [A_42] :
      ( k1_tops_1(A_42,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_119,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_93,plain,(
    ! [B_38,A_39] :
      ( v2_tops_1(B_38,A_39)
      | k1_tops_1(A_39,B_38) != k1_xboole_0
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_130,plain,(
    ! [A_44,A_45] :
      ( v2_tops_1(A_44,A_45)
      | k1_tops_1(A_45,A_44) != k1_xboole_0
      | ~ l1_pre_topc(A_45)
      | ~ r1_tarski(A_44,u1_struct_0(A_45)) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_145,plain,(
    ! [A_45] :
      ( v2_tops_1(k1_xboole_0,A_45)
      | k1_tops_1(A_45,k1_xboole_0) != k1_xboole_0
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_148,plain,(
    ! [A_48,B_49] :
      ( v1_xboole_0(k1_tops_1(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v2_tops_1(B_49,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [A_50,A_51] :
      ( v1_xboole_0(k1_tops_1(A_50,A_51))
      | ~ v2_tops_1(A_51,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ r1_tarski(A_51,u1_struct_0(A_50)) ) ),
    inference(resolution,[status(thm)],[c_12,c_148])).

tff(c_176,plain,(
    ! [A_54] :
      ( v1_xboole_0(k1_tops_1(A_54,k1_xboole_0))
      | ~ v2_tops_1(k1_xboole_0,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_154])).

tff(c_179,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v2_tops_1(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_176])).

tff(c_181,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v2_tops_1(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_179])).

tff(c_182,plain,(
    ~ v2_tops_1(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_185,plain,
    ( k1_tops_1('#skF_2',k1_xboole_0) != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_145,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_119,c_185])).

tff(c_190,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_227,plain,(
    ! [B_61,A_62] :
      ( v2_tex_2(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ v1_xboole_0(B_61)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_233,plain,(
    ! [A_63,A_64] :
      ( v2_tex_2(A_63,A_64)
      | ~ v1_xboole_0(A_63)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64)
      | ~ r1_tarski(A_63,u1_struct_0(A_64)) ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_245,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_xboole_0,A_64)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_8,c_233])).

tff(c_250,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_xboole_0,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_245])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_253,plain,(
    ! [A_67,B_68] :
      ( v3_tex_2('#skF_1'(A_67,B_68),A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_257,plain,(
    ! [A_67,A_4] :
      ( v3_tex_2('#skF_1'(A_67,A_4),A_67)
      | ~ v2_tex_2(A_4,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ r1_tarski(A_4,u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_12,c_253])).

tff(c_283,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_1'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v3_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [B_24] :
      ( ~ v3_tex_2(B_24,'#skF_2')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_305,plain,(
    ! [B_79] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_79),'#skF_2')
      | ~ v2_tex_2(B_79,'#skF_2')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_283,c_30])).

tff(c_318,plain,(
    ! [B_79] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_79),'#skF_2')
      | ~ v2_tex_2(B_79,'#skF_2')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_305])).

tff(c_321,plain,(
    ! [B_80] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_80),'#skF_2')
      | ~ v2_tex_2(B_80,'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_318])).

tff(c_335,plain,(
    ! [A_81] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',A_81),'#skF_2')
      | ~ v2_tex_2(A_81,'#skF_2')
      | ~ r1_tarski(A_81,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_321])).

tff(c_339,plain,(
    ! [A_4] :
      ( ~ v2_tex_2(A_4,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_257,c_335])).

tff(c_342,plain,(
    ! [A_4] :
      ( ~ v2_tex_2(A_4,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_4,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_339])).

tff(c_344,plain,(
    ! [A_82] :
      ( ~ v2_tex_2(A_82,'#skF_2')
      | ~ r1_tarski(A_82,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_342])).

tff(c_359,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_344])).

tff(c_370,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_250,c_359])).

tff(c_373,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_370])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:30:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.32  %$ v3_tex_2 > v2_tops_1 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.32  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.53/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.32  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.53/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.53/1.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.53/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.32  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.32  
% 2.53/1.34  tff(f_113, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.53/1.34  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.53/1.34  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.53/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.34  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.53/1.34  tff(f_45, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 2.53/1.34  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.53/1.34  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.53/1.34  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.34  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.34  tff(c_88, plain, (![A_36, B_37]: (r1_tarski(k1_tops_1(A_36, B_37), B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.34  tff(c_99, plain, (![A_40, A_41]: (r1_tarski(k1_tops_1(A_40, A_41), A_41) | ~l1_pre_topc(A_40) | ~r1_tarski(A_41, u1_struct_0(A_40)))), inference(resolution, [status(thm)], [c_12, c_88])).
% 2.53/1.34  tff(c_65, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.34  tff(c_74, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_65])).
% 2.53/1.34  tff(c_103, plain, (![A_40]: (k1_tops_1(A_40, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_40) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_40)))), inference(resolution, [status(thm)], [c_99, c_74])).
% 2.53/1.34  tff(c_115, plain, (![A_42]: (k1_tops_1(A_42, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_103])).
% 2.53/1.34  tff(c_119, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_115])).
% 2.53/1.34  tff(c_93, plain, (![B_38, A_39]: (v2_tops_1(B_38, A_39) | k1_tops_1(A_39, B_38)!=k1_xboole_0 | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.34  tff(c_130, plain, (![A_44, A_45]: (v2_tops_1(A_44, A_45) | k1_tops_1(A_45, A_44)!=k1_xboole_0 | ~l1_pre_topc(A_45) | ~r1_tarski(A_44, u1_struct_0(A_45)))), inference(resolution, [status(thm)], [c_12, c_93])).
% 2.53/1.34  tff(c_145, plain, (![A_45]: (v2_tops_1(k1_xboole_0, A_45) | k1_tops_1(A_45, k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_8, c_130])).
% 2.53/1.34  tff(c_148, plain, (![A_48, B_49]: (v1_xboole_0(k1_tops_1(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~v2_tops_1(B_49, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.34  tff(c_154, plain, (![A_50, A_51]: (v1_xboole_0(k1_tops_1(A_50, A_51)) | ~v2_tops_1(A_51, A_50) | ~l1_pre_topc(A_50) | ~r1_tarski(A_51, u1_struct_0(A_50)))), inference(resolution, [status(thm)], [c_12, c_148])).
% 2.53/1.34  tff(c_176, plain, (![A_54]: (v1_xboole_0(k1_tops_1(A_54, k1_xboole_0)) | ~v2_tops_1(k1_xboole_0, A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_8, c_154])).
% 2.53/1.34  tff(c_179, plain, (v1_xboole_0(k1_xboole_0) | ~v2_tops_1(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_119, c_176])).
% 2.53/1.34  tff(c_181, plain, (v1_xboole_0(k1_xboole_0) | ~v2_tops_1(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_179])).
% 2.53/1.34  tff(c_182, plain, (~v2_tops_1(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_181])).
% 2.53/1.34  tff(c_185, plain, (k1_tops_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_145, c_182])).
% 2.53/1.34  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_119, c_185])).
% 2.53/1.34  tff(c_190, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_181])).
% 2.53/1.34  tff(c_227, plain, (![B_61, A_62]: (v2_tex_2(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~v1_xboole_0(B_61) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.34  tff(c_233, plain, (![A_63, A_64]: (v2_tex_2(A_63, A_64) | ~v1_xboole_0(A_63) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64) | ~r1_tarski(A_63, u1_struct_0(A_64)))), inference(resolution, [status(thm)], [c_12, c_227])).
% 2.53/1.34  tff(c_245, plain, (![A_64]: (v2_tex_2(k1_xboole_0, A_64) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_8, c_233])).
% 2.53/1.34  tff(c_250, plain, (![A_64]: (v2_tex_2(k1_xboole_0, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_245])).
% 2.53/1.34  tff(c_34, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_253, plain, (![A_67, B_68]: (v3_tex_2('#skF_1'(A_67, B_68), A_67) | ~v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.53/1.34  tff(c_257, plain, (![A_67, A_4]: (v3_tex_2('#skF_1'(A_67, A_4), A_67) | ~v2_tex_2(A_4, A_67) | ~l1_pre_topc(A_67) | ~v3_tdlat_3(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~r1_tarski(A_4, u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_12, c_253])).
% 2.53/1.34  tff(c_283, plain, (![A_78, B_79]: (m1_subset_1('#skF_1'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v3_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.53/1.34  tff(c_30, plain, (![B_24]: (~v3_tex_2(B_24, '#skF_2') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_305, plain, (![B_79]: (~v3_tex_2('#skF_1'('#skF_2', B_79), '#skF_2') | ~v2_tex_2(B_79, '#skF_2') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_283, c_30])).
% 2.53/1.34  tff(c_318, plain, (![B_79]: (~v3_tex_2('#skF_1'('#skF_2', B_79), '#skF_2') | ~v2_tex_2(B_79, '#skF_2') | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_305])).
% 2.53/1.34  tff(c_321, plain, (![B_80]: (~v3_tex_2('#skF_1'('#skF_2', B_80), '#skF_2') | ~v2_tex_2(B_80, '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_318])).
% 2.53/1.34  tff(c_335, plain, (![A_81]: (~v3_tex_2('#skF_1'('#skF_2', A_81), '#skF_2') | ~v2_tex_2(A_81, '#skF_2') | ~r1_tarski(A_81, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_321])).
% 2.53/1.34  tff(c_339, plain, (![A_4]: (~v2_tex_2(A_4, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_4, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_257, c_335])).
% 2.53/1.34  tff(c_342, plain, (![A_4]: (~v2_tex_2(A_4, '#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_4, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_339])).
% 2.53/1.34  tff(c_344, plain, (![A_82]: (~v2_tex_2(A_82, '#skF_2') | ~r1_tarski(A_82, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_342])).
% 2.53/1.34  tff(c_359, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_8, c_344])).
% 2.53/1.34  tff(c_370, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_250, c_359])).
% 2.53/1.34  tff(c_373, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_370])).
% 2.53/1.34  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_373])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 60
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 1
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 4
% 2.53/1.34  #Demod        : 30
% 2.53/1.34  #Tautology    : 11
% 2.53/1.34  #SimpNegUnit  : 5
% 2.53/1.34  #BackRed      : 0
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.30
% 2.53/1.34  Parsing              : 0.17
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.28
% 2.53/1.34  Inferencing          : 0.11
% 2.53/1.34  Reduction            : 0.07
% 2.53/1.34  Demodulation         : 0.05
% 2.53/1.34  BG Simplification    : 0.01
% 2.53/1.34  Subsumption          : 0.06
% 2.53/1.34  Abstraction          : 0.01
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.61
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
