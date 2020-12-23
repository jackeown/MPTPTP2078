%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 631 expanded)
%              Number of leaves         :   48 ( 232 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (1614 expanded)
%              Number of equality atoms :   22 ( 213 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_188,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_154,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_32,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_107,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_103])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_64])).

tff(c_24,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_456,plain,(
    ! [A_124,B_125] :
      ( r2_hidden(A_124,B_125)
      | v1_xboole_0(B_125)
      | ~ m1_subset_1(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_460,plain,(
    ! [A_124,A_3] :
      ( r1_tarski(A_124,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_124,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_456,c_8])).

tff(c_464,plain,(
    ! [A_126,A_127] :
      ( r1_tarski(A_126,A_127)
      | ~ m1_subset_1(A_126,k1_zfmisc_1(A_127)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_460])).

tff(c_468,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_108,c_464])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_471,plain,
    ( k2_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_468,c_2])).

tff(c_472,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_543,plain,(
    ! [B_149,A_150] :
      ( v3_pre_topc(B_149,A_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ v1_tdlat_3(A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_553,plain,(
    ! [B_149] :
      ( v3_pre_topc(B_149,'#skF_4')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v1_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_543])).

tff(c_558,plain,(
    ! [B_151] :
      ( v3_pre_topc(B_151,'#skF_4')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_68,c_553])).

tff(c_566,plain,(
    ! [B_10] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_10),'#skF_4')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_558])).

tff(c_850,plain,(
    ! [B_201,A_202] :
      ( v4_pre_topc(B_201,A_202)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_202),B_201),A_202)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_856,plain,(
    ! [B_201] :
      ( v4_pre_topc(B_201,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_201),'#skF_4')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_850])).

tff(c_860,plain,(
    ! [B_203] :
      ( v4_pre_topc(B_203,'#skF_4')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'),B_203),'#skF_4')
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_107,c_856])).

tff(c_865,plain,(
    ! [B_204] :
      ( v4_pre_topc(B_204,'#skF_4')
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_566,c_860])).

tff(c_874,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_865])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_568,plain,(
    ! [A_152,B_153] :
      ( k2_pre_topc(A_152,B_153) = u1_struct_0(A_152)
      | ~ v1_tops_1(B_153,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_578,plain,(
    ! [B_153] :
      ( k2_pre_topc('#skF_4',B_153) = u1_struct_0('#skF_4')
      | ~ v1_tops_1(B_153,'#skF_4')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_568])).

tff(c_584,plain,(
    ! [B_155] :
      ( k2_pre_topc('#skF_4',B_155) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_155,'#skF_4')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_107,c_578])).

tff(c_593,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = k2_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_584])).

tff(c_594,plain,(
    ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_567,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_558])).

tff(c_74,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_113,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_74])).

tff(c_114,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_80,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_115,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_80])).

tff(c_116,plain,(
    ~ v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_115])).

tff(c_146,plain,(
    ! [B_67,A_68] :
      ( v1_subset_1(B_67,A_68)
      | B_67 = A_68
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_149,plain,
    ( v1_subset_1('#skF_5',k2_struct_0('#skF_4'))
    | k2_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_108,c_146])).

tff(c_152,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_149])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_tops_1(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_161,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_34])).

tff(c_165,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_161])).

tff(c_155,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_108])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_156,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_107])).

tff(c_357,plain,(
    ! [B_106,A_107] :
      ( v2_tex_2(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v1_tdlat_3(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_367,plain,(
    ! [B_106] :
      ( v2_tex_2(B_106,'#skF_4')
      | ~ m1_subset_1(B_106,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_357])).

tff(c_371,plain,(
    ! [B_106] :
      ( v2_tex_2(B_106,'#skF_4')
      | ~ m1_subset_1(B_106,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_367])).

tff(c_373,plain,(
    ! [B_108] :
      ( v2_tex_2(B_108,'#skF_4')
      | ~ m1_subset_1(B_108,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_371])).

tff(c_382,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_373])).

tff(c_409,plain,(
    ! [B_114,A_115] :
      ( v3_tex_2(B_114,A_115)
      | ~ v2_tex_2(B_114,A_115)
      | ~ v1_tops_1(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_419,plain,(
    ! [B_114] :
      ( v3_tex_2(B_114,'#skF_4')
      | ~ v2_tex_2(B_114,'#skF_4')
      | ~ v1_tops_1(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_409])).

tff(c_423,plain,(
    ! [B_114] :
      ( v3_tex_2(B_114,'#skF_4')
      | ~ v2_tex_2(B_114,'#skF_4')
      | ~ v1_tops_1(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_419])).

tff(c_426,plain,(
    ! [B_117] :
      ( v3_tex_2(B_117,'#skF_4')
      | ~ v2_tex_2(B_117,'#skF_4')
      | ~ v1_tops_1(B_117,'#skF_4')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_423])).

tff(c_433,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_426])).

tff(c_437,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_382,c_433])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_437])).

tff(c_441,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_767,plain,(
    ! [B_188,A_189] :
      ( v1_tops_1(B_188,A_189)
      | ~ v3_tex_2(B_188,A_189)
      | ~ v3_pre_topc(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_777,plain,(
    ! [B_188] :
      ( v1_tops_1(B_188,'#skF_4')
      | ~ v3_tex_2(B_188,'#skF_4')
      | ~ v3_pre_topc(B_188,'#skF_4')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_767])).

tff(c_781,plain,(
    ! [B_188] :
      ( v1_tops_1(B_188,'#skF_4')
      | ~ v3_tex_2(B_188,'#skF_4')
      | ~ v3_pre_topc(B_188,'#skF_4')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_777])).

tff(c_783,plain,(
    ! [B_190] :
      ( v1_tops_1(B_190,'#skF_4')
      | ~ v3_tex_2(B_190,'#skF_4')
      | ~ v3_pre_topc(B_190,'#skF_4')
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_781])).

tff(c_790,plain,
    ( v1_tops_1('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_783])).

tff(c_794,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_441,c_790])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_794])).

tff(c_797,plain,(
    k2_pre_topc('#skF_4','#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_1075,plain,(
    ! [A_242,C_243,B_244] :
      ( r1_tarski(k2_pre_topc(A_242,C_243),B_244)
      | ~ r1_tarski(C_243,B_244)
      | ~ v4_pre_topc(B_244,A_242)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1082,plain,(
    ! [C_243,B_244] :
      ( r1_tarski(k2_pre_topc('#skF_4',C_243),B_244)
      | ~ r1_tarski(C_243,B_244)
      | ~ v4_pre_topc(B_244,'#skF_4')
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_1075])).

tff(c_1104,plain,(
    ! [C_251,B_252] :
      ( r1_tarski(k2_pre_topc('#skF_4',C_251),B_252)
      | ~ r1_tarski(C_251,B_252)
      | ~ v4_pre_topc(B_252,'#skF_4')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_107,c_1082])).

tff(c_1109,plain,(
    ! [B_252] :
      ( r1_tarski(k2_pre_topc('#skF_4','#skF_5'),B_252)
      | ~ r1_tarski('#skF_5',B_252)
      | ~ v4_pre_topc(B_252,'#skF_4')
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_108,c_1104])).

tff(c_1113,plain,(
    ! [B_253] :
      ( r1_tarski(k2_struct_0('#skF_4'),B_253)
      | ~ r1_tarski('#skF_5',B_253)
      | ~ v4_pre_topc(B_253,'#skF_4')
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_1109])).

tff(c_1120,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),'#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_1113])).

tff(c_1124,plain,(
    r1_tarski(k2_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_6,c_1120])).

tff(c_1126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_1124])).

tff(c_1127,plain,(
    k2_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_440,plain,(
    v1_subset_1('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_1131,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_440])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  
% 3.43/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.43/1.62  
% 3.43/1.62  %Foreground sorts:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Background operators:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Foreground operators:
% 3.43/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.62  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.43/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.43/1.62  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.43/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.43/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.62  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.43/1.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.43/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.43/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.43/1.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.62  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.43/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.43/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.43/1.62  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.43/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.43/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.62  
% 3.86/1.64  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.86/1.64  tff(f_50, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.86/1.64  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.86/1.64  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.64  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.86/1.64  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.86/1.64  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.86/1.64  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.86/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.86/1.64  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.86/1.64  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 3.86/1.64  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.86/1.64  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.86/1.64  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.86/1.64  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => v1_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_tops_1)).
% 3.86/1.64  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.86/1.64  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.86/1.64  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.86/1.64  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 3.86/1.64  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.86/1.64  tff(c_26, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.64  tff(c_81, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 3.86/1.64  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_32, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.86/1.64  tff(c_96, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.64  tff(c_103, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_32, c_96])).
% 3.86/1.64  tff(c_107, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_103])).
% 3.86/1.64  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_64])).
% 3.86/1.64  tff(c_24, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.86/1.64  tff(c_456, plain, (![A_124, B_125]: (r2_hidden(A_124, B_125) | v1_xboole_0(B_125) | ~m1_subset_1(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.86/1.64  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.64  tff(c_460, plain, (![A_124, A_3]: (r1_tarski(A_124, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_124, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_456, c_8])).
% 3.86/1.64  tff(c_464, plain, (![A_126, A_127]: (r1_tarski(A_126, A_127) | ~m1_subset_1(A_126, k1_zfmisc_1(A_127)))), inference(negUnitSimplification, [status(thm)], [c_24, c_460])).
% 3.86/1.64  tff(c_468, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_464])).
% 3.86/1.64  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.64  tff(c_471, plain, (k2_struct_0('#skF_4')='#skF_5' | ~r1_tarski(k2_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_468, c_2])).
% 3.86/1.64  tff(c_472, plain, (~r1_tarski(k2_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_471])).
% 3.86/1.64  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.86/1.64  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_68, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_543, plain, (![B_149, A_150]: (v3_pre_topc(B_149, A_150) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~v1_tdlat_3(A_150) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.86/1.64  tff(c_553, plain, (![B_149]: (v3_pre_topc(B_149, '#skF_4') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_543])).
% 3.86/1.64  tff(c_558, plain, (![B_151]: (v3_pre_topc(B_151, '#skF_4') | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_68, c_553])).
% 3.86/1.64  tff(c_566, plain, (![B_10]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_10), '#skF_4') | ~m1_subset_1(B_10, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_22, c_558])).
% 3.86/1.64  tff(c_850, plain, (![B_201, A_202]: (v4_pre_topc(B_201, A_202) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_202), B_201), A_202) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.64  tff(c_856, plain, (![B_201]: (v4_pre_topc(B_201, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_201), '#skF_4') | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_850])).
% 3.86/1.64  tff(c_860, plain, (![B_203]: (v4_pre_topc(B_203, '#skF_4') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_4'), B_203), '#skF_4') | ~m1_subset_1(B_203, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_107, c_856])).
% 3.86/1.64  tff(c_865, plain, (![B_204]: (v4_pre_topc(B_204, '#skF_4') | ~m1_subset_1(B_204, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_566, c_860])).
% 3.86/1.64  tff(c_874, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_865])).
% 3.86/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.64  tff(c_568, plain, (![A_152, B_153]: (k2_pre_topc(A_152, B_153)=u1_struct_0(A_152) | ~v1_tops_1(B_153, A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.86/1.64  tff(c_578, plain, (![B_153]: (k2_pre_topc('#skF_4', B_153)=u1_struct_0('#skF_4') | ~v1_tops_1(B_153, '#skF_4') | ~m1_subset_1(B_153, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_568])).
% 3.86/1.64  tff(c_584, plain, (![B_155]: (k2_pre_topc('#skF_4', B_155)=k2_struct_0('#skF_4') | ~v1_tops_1(B_155, '#skF_4') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_107, c_578])).
% 3.86/1.64  tff(c_593, plain, (k2_pre_topc('#skF_4', '#skF_5')=k2_struct_0('#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_584])).
% 3.86/1.64  tff(c_594, plain, (~v1_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_593])).
% 3.86/1.64  tff(c_567, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_558])).
% 3.86/1.64  tff(c_74, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_113, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_74])).
% 3.86/1.64  tff(c_114, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_113])).
% 3.86/1.64  tff(c_80, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_115, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_80])).
% 3.86/1.64  tff(c_116, plain, (~v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_114, c_115])).
% 3.86/1.64  tff(c_146, plain, (![B_67, A_68]: (v1_subset_1(B_67, A_68) | B_67=A_68 | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.64  tff(c_149, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4')) | k2_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_108, c_146])).
% 3.86/1.64  tff(c_152, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_116, c_149])).
% 3.86/1.64  tff(c_34, plain, (![A_17]: (v1_tops_1(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.86/1.64  tff(c_161, plain, (v1_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 3.86/1.64  tff(c_165, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_161])).
% 3.86/1.64  tff(c_155, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_108])).
% 3.86/1.64  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.86/1.64  tff(c_156, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_107])).
% 3.86/1.64  tff(c_357, plain, (![B_106, A_107]: (v2_tex_2(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v1_tdlat_3(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.86/1.64  tff(c_367, plain, (![B_106]: (v2_tex_2(B_106, '#skF_4') | ~m1_subset_1(B_106, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_357])).
% 3.86/1.64  tff(c_371, plain, (![B_106]: (v2_tex_2(B_106, '#skF_4') | ~m1_subset_1(B_106, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_367])).
% 3.86/1.64  tff(c_373, plain, (![B_108]: (v2_tex_2(B_108, '#skF_4') | ~m1_subset_1(B_108, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_371])).
% 3.86/1.64  tff(c_382, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_155, c_373])).
% 3.86/1.64  tff(c_409, plain, (![B_114, A_115]: (v3_tex_2(B_114, A_115) | ~v2_tex_2(B_114, A_115) | ~v1_tops_1(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.86/1.64  tff(c_419, plain, (![B_114]: (v3_tex_2(B_114, '#skF_4') | ~v2_tex_2(B_114, '#skF_4') | ~v1_tops_1(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_409])).
% 3.86/1.64  tff(c_423, plain, (![B_114]: (v3_tex_2(B_114, '#skF_4') | ~v2_tex_2(B_114, '#skF_4') | ~v1_tops_1(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_419])).
% 3.86/1.64  tff(c_426, plain, (![B_117]: (v3_tex_2(B_117, '#skF_4') | ~v2_tex_2(B_117, '#skF_4') | ~v1_tops_1(B_117, '#skF_4') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_423])).
% 3.86/1.64  tff(c_433, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~v1_tops_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_155, c_426])).
% 3.86/1.64  tff(c_437, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_382, c_433])).
% 3.86/1.64  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_437])).
% 3.86/1.64  tff(c_441, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_113])).
% 3.86/1.64  tff(c_767, plain, (![B_188, A_189]: (v1_tops_1(B_188, A_189) | ~v3_tex_2(B_188, A_189) | ~v3_pre_topc(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.86/1.64  tff(c_777, plain, (![B_188]: (v1_tops_1(B_188, '#skF_4') | ~v3_tex_2(B_188, '#skF_4') | ~v3_pre_topc(B_188, '#skF_4') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_767])).
% 3.86/1.64  tff(c_781, plain, (![B_188]: (v1_tops_1(B_188, '#skF_4') | ~v3_tex_2(B_188, '#skF_4') | ~v3_pre_topc(B_188, '#skF_4') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_777])).
% 3.86/1.64  tff(c_783, plain, (![B_190]: (v1_tops_1(B_190, '#skF_4') | ~v3_tex_2(B_190, '#skF_4') | ~v3_pre_topc(B_190, '#skF_4') | ~m1_subset_1(B_190, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_781])).
% 3.86/1.64  tff(c_790, plain, (v1_tops_1('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_783])).
% 3.86/1.64  tff(c_794, plain, (v1_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_567, c_441, c_790])).
% 3.86/1.64  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_794])).
% 3.86/1.64  tff(c_797, plain, (k2_pre_topc('#skF_4', '#skF_5')=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_593])).
% 3.86/1.64  tff(c_1075, plain, (![A_242, C_243, B_244]: (r1_tarski(k2_pre_topc(A_242, C_243), B_244) | ~r1_tarski(C_243, B_244) | ~v4_pre_topc(B_244, A_242) | ~m1_subset_1(C_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.86/1.64  tff(c_1082, plain, (![C_243, B_244]: (r1_tarski(k2_pre_topc('#skF_4', C_243), B_244) | ~r1_tarski(C_243, B_244) | ~v4_pre_topc(B_244, '#skF_4') | ~m1_subset_1(C_243, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_1075])).
% 3.86/1.64  tff(c_1104, plain, (![C_251, B_252]: (r1_tarski(k2_pre_topc('#skF_4', C_251), B_252) | ~r1_tarski(C_251, B_252) | ~v4_pre_topc(B_252, '#skF_4') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_107, c_1082])).
% 3.86/1.64  tff(c_1109, plain, (![B_252]: (r1_tarski(k2_pre_topc('#skF_4', '#skF_5'), B_252) | ~r1_tarski('#skF_5', B_252) | ~v4_pre_topc(B_252, '#skF_4') | ~m1_subset_1(B_252, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_108, c_1104])).
% 3.86/1.64  tff(c_1113, plain, (![B_253]: (r1_tarski(k2_struct_0('#skF_4'), B_253) | ~r1_tarski('#skF_5', B_253) | ~v4_pre_topc(B_253, '#skF_4') | ~m1_subset_1(B_253, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_797, c_1109])).
% 3.86/1.64  tff(c_1120, plain, (r1_tarski(k2_struct_0('#skF_4'), '#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_108, c_1113])).
% 3.86/1.64  tff(c_1124, plain, (r1_tarski(k2_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_874, c_6, c_1120])).
% 3.86/1.64  tff(c_1126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_1124])).
% 3.86/1.64  tff(c_1127, plain, (k2_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_471])).
% 3.86/1.64  tff(c_440, plain, (v1_subset_1('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_113])).
% 3.86/1.64  tff(c_1131, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_440])).
% 3.86/1.64  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_1131])).
% 3.86/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.64  
% 3.86/1.64  Inference rules
% 3.86/1.64  ----------------------
% 3.86/1.64  #Ref     : 0
% 3.86/1.64  #Sup     : 195
% 3.86/1.64  #Fact    : 0
% 3.86/1.64  #Define  : 0
% 3.86/1.64  #Split   : 3
% 3.86/1.64  #Chain   : 0
% 3.86/1.64  #Close   : 0
% 3.86/1.64  
% 3.86/1.64  Ordering : KBO
% 3.86/1.64  
% 3.86/1.64  Simplification rules
% 3.86/1.64  ----------------------
% 3.86/1.64  #Subsume      : 20
% 3.86/1.64  #Demod        : 155
% 3.86/1.64  #Tautology    : 64
% 3.86/1.64  #SimpNegUnit  : 23
% 3.86/1.64  #BackRed      : 9
% 3.86/1.64  
% 3.86/1.64  #Partial instantiations: 0
% 3.86/1.64  #Strategies tried      : 1
% 3.86/1.64  
% 3.86/1.64  Timing (in seconds)
% 3.86/1.64  ----------------------
% 3.86/1.64  Preprocessing        : 0.35
% 3.86/1.64  Parsing              : 0.18
% 3.86/1.64  CNF conversion       : 0.03
% 3.86/1.64  Main loop            : 0.47
% 3.86/1.64  Inferencing          : 0.18
% 3.86/1.64  Reduction            : 0.14
% 3.86/1.64  Demodulation         : 0.09
% 3.86/1.64  BG Simplification    : 0.03
% 3.86/1.64  Subsumption          : 0.09
% 3.86/1.64  Abstraction          : 0.02
% 3.86/1.64  MUC search           : 0.00
% 3.86/1.64  Cooper               : 0.00
% 3.86/1.64  Total                : 0.87
% 3.86/1.64  Index Insertion      : 0.00
% 3.86/1.64  Index Deletion       : 0.00
% 3.86/1.64  Index Matching       : 0.00
% 3.86/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
