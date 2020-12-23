%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:27 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 159 expanded)
%              Number of leaves         :   40 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 501 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_62,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_6] : k3_subset_1(A_6,k3_subset_1(A_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_121,plain,(
    ! [A_6] : k3_subset_1(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_118])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_187,plain,(
    ! [A_57,B_58] :
      ( k2_pre_topc(A_57,B_58) = B_58
      | ~ v4_pre_topc(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_196,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_187])).

tff(c_205,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_196])).

tff(c_207,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_89,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_287,plain,(
    ! [B_75,A_76] :
      ( v4_pre_topc(B_75,A_76)
      | ~ v3_pre_topc(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v3_tdlat_3(A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_296,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_287])).

tff(c_305,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_89,c_296])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_305])).

tff(c_308,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_317,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = u1_struct_0(A_81)
      | ~ v1_tops_1(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_326,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_317])).

tff(c_335,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_308,c_326])).

tff(c_337,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_48,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_471,plain,(
    ! [B_104,A_105] :
      ( v1_tops_1(B_104,A_105)
      | ~ v3_tex_2(B_104,A_105)
      | ~ v3_pre_topc(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_480,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_489,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_89,c_48,c_480])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_337,c_489])).

tff(c_492,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_46,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_90,plain,(
    ! [B_37,A_38] :
      ( ~ v1_subset_1(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_99,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_166,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(k3_subset_1(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55))
      | ~ v1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_166])).

tff(c_183,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_175])).

tff(c_184,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_183])).

tff(c_494,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_184])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_121,c_494])).

tff(c_504,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_503,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_719,plain,(
    ! [B_147,A_148] :
      ( v3_pre_topc(B_147,A_148)
      | ~ v4_pre_topc(B_147,A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v3_tdlat_3(A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_728,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_719])).

tff(c_737,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_503,c_728])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.44  
% 3.03/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.44  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.03/1.44  
% 3.03/1.44  %Foreground sorts:
% 3.03/1.44  
% 3.03/1.44  
% 3.03/1.44  %Background operators:
% 3.03/1.44  
% 3.03/1.44  
% 3.03/1.44  %Foreground operators:
% 3.03/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.03/1.44  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.03/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.03/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.44  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.03/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.03/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.03/1.44  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.03/1.44  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.03/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.44  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.03/1.44  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.03/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.44  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.03/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.03/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.03/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.44  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.03/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.44  
% 3.03/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.03/1.46  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.03/1.46  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.03/1.46  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.03/1.46  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.03/1.46  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.03/1.46  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 3.03/1.46  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.03/1.46  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 3.03/1.46  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.03/1.46  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.03/1.46  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.03/1.46  tff(f_86, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 3.03/1.46  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.03/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.03/1.46  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.03/1.46  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.03/1.46  tff(c_10, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.03/1.46  tff(c_61, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.03/1.46  tff(c_62, plain, (![A_5]: (k3_subset_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 3.03/1.46  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.46  tff(c_114, plain, (![A_49, B_50]: (k3_subset_1(A_49, k3_subset_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.03/1.46  tff(c_118, plain, (![A_6]: (k3_subset_1(A_6, k3_subset_1(A_6, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_114])).
% 3.03/1.46  tff(c_121, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_118])).
% 3.03/1.46  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_187, plain, (![A_57, B_58]: (k2_pre_topc(A_57, B_58)=B_58 | ~v4_pre_topc(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.46  tff(c_196, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_187])).
% 3.03/1.46  tff(c_205, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_196])).
% 3.03/1.46  tff(c_207, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_205])).
% 3.03/1.46  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_56, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_50, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_89, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.03/1.46  tff(c_287, plain, (![B_75, A_76]: (v4_pre_topc(B_75, A_76) | ~v3_pre_topc(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~v3_tdlat_3(A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.03/1.46  tff(c_296, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_287])).
% 3.03/1.46  tff(c_305, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_89, c_296])).
% 3.03/1.46  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_305])).
% 3.03/1.46  tff(c_308, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_205])).
% 3.03/1.46  tff(c_317, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=u1_struct_0(A_81) | ~v1_tops_1(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.03/1.46  tff(c_326, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_317])).
% 3.03/1.46  tff(c_335, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_308, c_326])).
% 3.03/1.46  tff(c_337, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_335])).
% 3.03/1.46  tff(c_48, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_471, plain, (![B_104, A_105]: (v1_tops_1(B_104, A_105) | ~v3_tex_2(B_104, A_105) | ~v3_pre_topc(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.03/1.46  tff(c_480, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_471])).
% 3.03/1.46  tff(c_489, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_89, c_48, c_480])).
% 3.03/1.46  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_337, c_489])).
% 3.03/1.46  tff(c_492, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_335])).
% 3.03/1.46  tff(c_46, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.03/1.46  tff(c_90, plain, (![B_37, A_38]: (~v1_subset_1(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.03/1.46  tff(c_93, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_90])).
% 3.03/1.46  tff(c_99, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_93])).
% 3.03/1.46  tff(c_166, plain, (![A_55, B_56]: (~v1_xboole_0(k3_subset_1(A_55, B_56)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)) | ~v1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.03/1.46  tff(c_175, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_166])).
% 3.03/1.46  tff(c_183, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_175])).
% 3.03/1.46  tff(c_184, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_99, c_183])).
% 3.03/1.46  tff(c_494, plain, (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_184])).
% 3.03/1.46  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_121, c_494])).
% 3.03/1.46  tff(c_504, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.03/1.46  tff(c_503, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.03/1.46  tff(c_719, plain, (![B_147, A_148]: (v3_pre_topc(B_147, A_148) | ~v4_pre_topc(B_147, A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~v3_tdlat_3(A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.03/1.46  tff(c_728, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_719])).
% 3.03/1.46  tff(c_737, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_503, c_728])).
% 3.03/1.46  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_737])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 0
% 3.03/1.46  #Sup     : 135
% 3.03/1.46  #Fact    : 0
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 5
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 13
% 3.03/1.46  #Demod        : 64
% 3.03/1.46  #Tautology    : 44
% 3.03/1.46  #SimpNegUnit  : 9
% 3.03/1.46  #BackRed      : 6
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.03/1.46  Preprocessing        : 0.33
% 3.03/1.46  Parsing              : 0.18
% 3.03/1.46  CNF conversion       : 0.02
% 3.03/1.46  Main loop            : 0.35
% 3.03/1.46  Inferencing          : 0.14
% 3.03/1.46  Reduction            : 0.10
% 3.03/1.46  Demodulation         : 0.07
% 3.03/1.46  BG Simplification    : 0.02
% 3.03/1.46  Subsumption          : 0.04
% 3.03/1.46  Abstraction          : 0.02
% 3.03/1.46  MUC search           : 0.00
% 3.03/1.46  Cooper               : 0.00
% 3.03/1.46  Total                : 0.71
% 3.03/1.46  Index Insertion      : 0.00
% 3.03/1.46  Index Deletion       : 0.00
% 3.03/1.46  Index Matching       : 0.00
% 3.03/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
