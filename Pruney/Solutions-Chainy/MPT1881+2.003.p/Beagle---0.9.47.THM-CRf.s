%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 30.16s
% Output     : CNFRefutation 30.86s
% Verified   : 
% Statistics : Number of formulae       :  434 (50191 expanded)
%              Number of leaves         :   46 (16062 expanded)
%              Depth                    :   43
%              Number of atoms          : 1163 (163791 expanded)
%              Number of equality atoms :  120 (11484 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_54,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_179,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & ~ v1_zfmisc_1(B)
          & ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tex_2)).

tff(f_26,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117521,plain,(
    ! [B_3086,A_3087] :
      ( v1_xboole_0(B_3086)
      | ~ m1_subset_1(B_3086,k1_zfmisc_1(A_3087))
      | ~ v1_xboole_0(A_3087) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_117550,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_117521])).

tff(c_117551,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitLeft,[status(thm)],[c_117550])).

tff(c_16,plain,(
    ! [A_8] : v1_xboole_0('#skF_1'(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117551,c_16])).

tff(c_117562,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_117550])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_84,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_241,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_270,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_241])).

tff(c_271,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_16])).

tff(c_281,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_88,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_135,plain,(
    ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_44,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_3'(A_31))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_94,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_197,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_94])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_370,plain,(
    ! [B_95,A_96] :
      ( v1_subset_1(B_95,A_96)
      | B_95 = A_96
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_386,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_370])).

tff(c_399,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_386])).

tff(c_404,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_78])).

tff(c_82,plain,(
    v1_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1111,plain,(
    ! [B_162,A_163] :
      ( v2_tex_2(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v1_tdlat_3(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1126,plain,(
    ! [B_162] :
      ( v2_tex_2(B_162,'#skF_6')
      | ~ m1_subset_1(B_162,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v1_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1111])).

tff(c_1146,plain,(
    ! [B_162] :
      ( v2_tex_2(B_162,'#skF_6')
      | ~ m1_subset_1(B_162,k1_zfmisc_1('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1126])).

tff(c_1152,plain,(
    ! [B_164] :
      ( v2_tex_2(B_164,'#skF_6')
      | ~ m1_subset_1(B_164,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1146])).

tff(c_1187,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_404,c_1152])).

tff(c_63726,plain,(
    ! [A_1593,B_1594] :
      ( '#skF_4'(A_1593,B_1594) != B_1594
      | v3_tex_2(B_1594,A_1593)
      | ~ v2_tex_2(B_1594,A_1593)
      | ~ m1_subset_1(B_1594,k1_zfmisc_1(u1_struct_0(A_1593)))
      | ~ l1_pre_topc(A_1593) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_63741,plain,(
    ! [B_1594] :
      ( '#skF_4'('#skF_6',B_1594) != B_1594
      | v3_tex_2(B_1594,'#skF_6')
      | ~ v2_tex_2(B_1594,'#skF_6')
      | ~ m1_subset_1(B_1594,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_63726])).

tff(c_64102,plain,(
    ! [B_1620] :
      ( '#skF_4'('#skF_6',B_1620) != B_1620
      | v3_tex_2(B_1620,'#skF_6')
      | ~ v2_tex_2(B_1620,'#skF_6')
      | ~ m1_subset_1(B_1620,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_63741])).

tff(c_64117,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_404,c_64102])).

tff(c_64140,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_64117])).

tff(c_64141,plain,(
    '#skF_4'('#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_64140])).

tff(c_64008,plain,(
    ! [B_1615,A_1616] :
      ( r1_tarski(B_1615,'#skF_4'(A_1616,B_1615))
      | v3_tex_2(B_1615,A_1616)
      | ~ v2_tex_2(B_1615,A_1616)
      | ~ m1_subset_1(B_1615,k1_zfmisc_1(u1_struct_0(A_1616)))
      | ~ l1_pre_topc(A_1616) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64019,plain,(
    ! [B_1615] :
      ( r1_tarski(B_1615,'#skF_4'('#skF_6',B_1615))
      | v3_tex_2(B_1615,'#skF_6')
      | ~ v2_tex_2(B_1615,'#skF_6')
      | ~ m1_subset_1(B_1615,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_64008])).

tff(c_64449,plain,(
    ! [B_1646] :
      ( r1_tarski(B_1646,'#skF_4'('#skF_6',B_1646))
      | v3_tex_2(B_1646,'#skF_6')
      | ~ v2_tex_2(B_1646,'#skF_6')
      | ~ m1_subset_1(B_1646,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64019])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_3'(A_31),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_411,plain,
    ( m1_subset_1('#skF_3'('#skF_6'),k1_zfmisc_1('#skF_7'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_46])).

tff(c_417,plain,(
    m1_subset_1('#skF_3'('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_411])).

tff(c_550,plain,(
    ! [A_102,C_103,B_104] :
      ( m1_subset_1(A_102,C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_607,plain,(
    ! [A_109] :
      ( m1_subset_1(A_109,'#skF_7')
      | ~ r2_hidden(A_109,'#skF_3'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_417,c_550])).

tff(c_612,plain,(
    ! [B_2] :
      ( m1_subset_1(B_2,'#skF_7')
      | ~ m1_subset_1(B_2,'#skF_3'('#skF_6'))
      | v1_xboole_0('#skF_3'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_607])).

tff(c_729,plain,(
    v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_612])).

tff(c_8,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_666,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(k1_tarski(B_120),k1_zfmisc_1(A_121))
      | k1_xboole_0 = A_121
      | ~ m1_subset_1(B_120,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [B_22,A_20] :
      ( v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_745,plain,(
    ! [B_133,A_134] :
      ( v1_xboole_0(k1_tarski(B_133))
      | ~ v1_xboole_0(A_134)
      | k1_xboole_0 = A_134
      | ~ m1_subset_1(B_133,A_134) ) ),
    inference(resolution,[status(thm)],[c_666,c_34])).

tff(c_777,plain,(
    ! [B_2,A_1] :
      ( v1_xboole_0(k1_tarski(B_2))
      | k1_xboole_0 = A_1
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_745])).

tff(c_833,plain,(
    ! [A_137] :
      ( k1_xboole_0 = A_137
      | ~ v1_xboole_0(A_137) ) ),
    inference(splitLeft,[status(thm)],[c_777])).

tff(c_846,plain,(
    '#skF_3'('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_729,c_833])).

tff(c_269,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_241])).

tff(c_282,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_401,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_282])).

tff(c_50,plain,(
    ! [B_37,A_36] :
      ( v1_subset_1(B_37,A_36)
      | B_37 = A_36
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_509,plain,
    ( v1_subset_1('#skF_3'('#skF_6'),'#skF_7')
    | '#skF_3'('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_417,c_50])).

tff(c_515,plain,(
    '#skF_3'('#skF_6') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_529,plain,
    ( v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_44])).

tff(c_537,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_529])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_537])).

tff(c_541,plain,(
    '#skF_3'('#skF_6') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_873,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_541])).

tff(c_24,plain,(
    ! [A_13,B_14,C_18] :
      ( m1_subset_1('#skF_2'(A_13,B_14,C_18),A_13)
      | C_18 = B_14
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_741,plain,(
    ! [C_130,A_131,B_132] :
      ( r2_hidden(C_130,A_131)
      | ~ r2_hidden(C_130,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63789,plain,(
    ! [B_1597,A_1598,A_1599] :
      ( r2_hidden(B_1597,A_1598)
      | ~ m1_subset_1(A_1599,k1_zfmisc_1(A_1598))
      | ~ m1_subset_1(B_1597,A_1599)
      | v1_xboole_0(A_1599) ) ),
    inference(resolution,[status(thm)],[c_6,c_741])).

tff(c_63798,plain,(
    ! [B_1597] :
      ( r2_hidden(B_1597,'#skF_7')
      | ~ m1_subset_1(B_1597,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_404,c_63789])).

tff(c_63822,plain,(
    ! [B_1600] :
      ( r2_hidden(B_1600,'#skF_7')
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_63798])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_325,plain,(
    ! [C_90,B_91,A_92] :
      ( ~ v1_xboole_0(C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_342,plain,(
    ! [B_24,A_92,A_23] :
      ( ~ v1_xboole_0(B_24)
      | ~ r2_hidden(A_92,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_325])).

tff(c_63840,plain,(
    ! [B_24,B_1600] :
      ( ~ v1_xboole_0(B_24)
      | ~ r1_tarski('#skF_7',B_24)
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_63822,c_342])).

tff(c_63850,plain,(
    ! [B_1603] : ~ m1_subset_1(B_1603,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_63840])).

tff(c_63901,plain,(
    ! [C_1607,B_1608] :
      ( C_1607 = B_1608
      | ~ m1_subset_1(C_1607,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_1608,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_63850])).

tff(c_63932,plain,(
    ! [B_1609] :
      ( B_1609 = '#skF_7'
      | ~ m1_subset_1(B_1609,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_404,c_63901])).

tff(c_63959,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_63932])).

tff(c_63973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_63959])).

tff(c_63974,plain,(
    ! [B_24] :
      ( ~ v1_xboole_0(B_24)
      | ~ r1_tarski('#skF_7',B_24) ) ),
    inference(splitRight,[status(thm)],[c_63840])).

tff(c_64481,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_64449,c_63974])).

tff(c_64503,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_64481])).

tff(c_64504,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_64503])).

tff(c_64334,plain,(
    ! [A_1640,B_1641] :
      ( m1_subset_1('#skF_4'(A_1640,B_1641),k1_zfmisc_1(u1_struct_0(A_1640)))
      | v3_tex_2(B_1641,A_1640)
      | ~ v2_tex_2(B_1641,A_1640)
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0(A_1640)))
      | ~ l1_pre_topc(A_1640) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64376,plain,(
    ! [B_1641] :
      ( m1_subset_1('#skF_4'('#skF_6',B_1641),k1_zfmisc_1('#skF_7'))
      | v3_tex_2(B_1641,'#skF_6')
      | ~ v2_tex_2(B_1641,'#skF_6')
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_64334])).

tff(c_64395,plain,(
    ! [B_1641] :
      ( m1_subset_1('#skF_4'('#skF_6',B_1641),k1_zfmisc_1('#skF_7'))
      | v3_tex_2(B_1641,'#skF_6')
      | ~ v2_tex_2(B_1641,'#skF_6')
      | ~ m1_subset_1(B_1641,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_399,c_64376])).

tff(c_60,plain,(
    ! [A_38,B_44] :
      ( m1_subset_1('#skF_4'(A_38,B_44),k1_zfmisc_1(u1_struct_0(A_38)))
      | v3_tex_2(B_44,A_38)
      | ~ v2_tex_2(B_44,A_38)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69179,plain,(
    ! [A_1873,B_1874] :
      ( r1_tarski('#skF_4'(A_1873,B_1874),u1_struct_0(A_1873))
      | v3_tex_2(B_1874,A_1873)
      | ~ v2_tex_2(B_1874,A_1873)
      | ~ m1_subset_1(B_1874,k1_zfmisc_1(u1_struct_0(A_1873)))
      | ~ l1_pre_topc(A_1873) ) ),
    inference(resolution,[status(thm)],[c_64334,c_36])).

tff(c_69233,plain,(
    ! [B_1874] :
      ( r1_tarski('#skF_4'('#skF_6',B_1874),'#skF_7')
      | v3_tex_2(B_1874,'#skF_6')
      | ~ v2_tex_2(B_1874,'#skF_6')
      | ~ m1_subset_1(B_1874,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_69179])).

tff(c_72533,plain,(
    ! [B_1976] :
      ( r1_tarski('#skF_4'('#skF_6',B_1976),'#skF_7')
      | v3_tex_2(B_1976,'#skF_6')
      | ~ v2_tex_2(B_1976,'#skF_6')
      | ~ m1_subset_1(B_1976,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_399,c_69233])).

tff(c_64767,plain,(
    ! [A_1667,B_1668,C_1669] :
      ( r2_hidden('#skF_2'(A_1667,B_1668,C_1669),B_1668)
      | r2_hidden('#skF_2'(A_1667,B_1668,C_1669),C_1669)
      | C_1669 = B_1668
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_1667))
      | ~ m1_subset_1(B_1668,k1_zfmisc_1(A_1667)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_572,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,'#skF_7')
      | ~ r2_hidden(A_102,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_404,c_550])).

tff(c_64849,plain,(
    ! [A_1667,C_1669] :
      ( m1_subset_1('#skF_2'(A_1667,'#skF_7',C_1669),'#skF_7')
      | r2_hidden('#skF_2'(A_1667,'#skF_7',C_1669),C_1669)
      | C_1669 = '#skF_7'
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_1667))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_64767,c_572])).

tff(c_574,plain,(
    ! [A_102,B_24,A_23] :
      ( m1_subset_1(A_102,B_24)
      | ~ r2_hidden(A_102,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_550])).

tff(c_63839,plain,(
    ! [B_1600,B_24] :
      ( m1_subset_1(B_1600,B_24)
      | ~ r1_tarski('#skF_7',B_24)
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_63822,c_574])).

tff(c_64477,plain,(
    ! [B_1600] :
      ( m1_subset_1(B_1600,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1600,'#skF_7')
      | v3_tex_2('#skF_7','#skF_6')
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64449,c_63839])).

tff(c_64499,plain,(
    ! [B_1600] :
      ( m1_subset_1(B_1600,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1600,'#skF_7')
      | v3_tex_2('#skF_7','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_64477])).

tff(c_64500,plain,(
    ! [B_1600] :
      ( m1_subset_1(B_1600,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_64499])).

tff(c_40,plain,(
    ! [A_25,C_27,B_26] :
      ( m1_subset_1(A_25,C_27)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64678,plain,(
    ! [A_1661,A_1662,B_1663] :
      ( m1_subset_1(A_1661,A_1662)
      | ~ r2_hidden(A_1661,k1_tarski(B_1663))
      | k1_xboole_0 = A_1662
      | ~ m1_subset_1(B_1663,A_1662) ) ),
    inference(resolution,[status(thm)],[c_666,c_40])).

tff(c_67253,plain,(
    ! [B_1798,A_1799,B_1800] :
      ( m1_subset_1(B_1798,A_1799)
      | k1_xboole_0 = A_1799
      | ~ m1_subset_1(B_1800,A_1799)
      | ~ m1_subset_1(B_1798,k1_tarski(B_1800))
      | v1_xboole_0(k1_tarski(B_1800)) ) ),
    inference(resolution,[status(thm)],[c_6,c_64678])).

tff(c_67299,plain,(
    ! [B_1798,B_1600] :
      ( m1_subset_1(B_1798,'#skF_4'('#skF_6','#skF_7'))
      | '#skF_4'('#skF_6','#skF_7') = k1_xboole_0
      | ~ m1_subset_1(B_1798,k1_tarski(B_1600))
      | v1_xboole_0(k1_tarski(B_1600))
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64500,c_67253])).

tff(c_67621,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_67299])).

tff(c_67678,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67621,c_64504])).

tff(c_67684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_67678])).

tff(c_67686,plain,(
    '#skF_4'('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_67299])).

tff(c_691,plain,(
    ! [B_120,A_121] :
      ( v1_subset_1(k1_tarski(B_120),A_121)
      | k1_tarski(B_120) = A_121
      | k1_xboole_0 = A_121
      | ~ m1_subset_1(B_120,A_121) ) ),
    inference(resolution,[status(thm)],[c_666,c_50])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(k1_tarski(B_12),k1_zfmisc_1(A_11))
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_785,plain,(
    ! [B_135,A_136] :
      ( ~ v1_subset_1(B_135,A_136)
      | v1_xboole_0(B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_136))
      | ~ v1_zfmisc_1(A_136)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66579,plain,(
    ! [B_1762,A_1763] :
      ( ~ v1_subset_1(k1_tarski(B_1762),A_1763)
      | v1_xboole_0(k1_tarski(B_1762))
      | ~ v1_zfmisc_1(A_1763)
      | v1_xboole_0(A_1763)
      | k1_xboole_0 = A_1763
      | ~ m1_subset_1(B_1762,A_1763) ) ),
    inference(resolution,[status(thm)],[c_22,c_785])).

tff(c_68722,plain,(
    ! [B_1866,A_1867] :
      ( v1_xboole_0(k1_tarski(B_1866))
      | ~ v1_zfmisc_1(A_1867)
      | v1_xboole_0(A_1867)
      | k1_tarski(B_1866) = A_1867
      | k1_xboole_0 = A_1867
      | ~ m1_subset_1(B_1866,A_1867) ) ),
    inference(resolution,[status(thm)],[c_691,c_66579])).

tff(c_68736,plain,(
    ! [B_1600] :
      ( v1_xboole_0(k1_tarski(B_1600))
      | ~ v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | k1_tarski(B_1600) = '#skF_4'('#skF_6','#skF_7')
      | '#skF_4'('#skF_6','#skF_7') = k1_xboole_0
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64500,c_68722])).

tff(c_68773,plain,(
    ! [B_1600] :
      ( v1_xboole_0(k1_tarski(B_1600))
      | ~ v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
      | k1_tarski(B_1600) = '#skF_4'('#skF_6','#skF_7')
      | ~ m1_subset_1(B_1600,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67686,c_64504,c_68736])).

tff(c_68816,plain,(
    ~ v1_zfmisc_1('#skF_4'('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_68773])).

tff(c_453,plain,(
    ! [A_97] :
      ( m1_subset_1('#skF_5'(A_97),k1_zfmisc_1(A_97))
      | v1_zfmisc_1(A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1081,plain,(
    ! [A_156] :
      ( v1_subset_1('#skF_5'(A_156),A_156)
      | '#skF_5'(A_156) = A_156
      | v1_zfmisc_1(A_156)
      | v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_453,c_50])).

tff(c_66,plain,(
    ! [A_48] :
      ( ~ v1_subset_1('#skF_5'(A_48),A_48)
      | v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1085,plain,(
    ! [A_156] :
      ( '#skF_5'(A_156) = A_156
      | v1_zfmisc_1(A_156)
      | v1_xboole_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_1081,c_66])).

tff(c_68819,plain,
    ( '#skF_5'('#skF_4'('#skF_6','#skF_7')) = '#skF_4'('#skF_6','#skF_7')
    | v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1085,c_68816])).

tff(c_68822,plain,(
    '#skF_5'('#skF_4'('#skF_6','#skF_7')) = '#skF_4'('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_68819])).

tff(c_72,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_5'(A_48),k1_zfmisc_1(A_48))
      | v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_571,plain,(
    ! [A_102,A_48] :
      ( m1_subset_1(A_102,A_48)
      | ~ r2_hidden(A_102,'#skF_5'(A_48))
      | v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_72,c_550])).

tff(c_68849,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,'#skF_4'('#skF_6','#skF_7'))
      | ~ r2_hidden(A_102,'#skF_4'('#skF_6','#skF_7'))
      | v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68822,c_571])).

tff(c_69067,plain,(
    ! [A_1871] :
      ( m1_subset_1(A_1871,'#skF_4'('#skF_6','#skF_7'))
      | ~ r2_hidden(A_1871,'#skF_4'('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_68816,c_68849])).

tff(c_69082,plain,(
    ! [A_1667] :
      ( m1_subset_1('#skF_2'(A_1667,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_4'('#skF_6','#skF_7'))
      | m1_subset_1('#skF_2'(A_1667,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_7')
      | '#skF_4'('#skF_6','#skF_7') = '#skF_7'
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1667))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_64849,c_69067])).

tff(c_69940,plain,(
    ! [A_1891] :
      ( m1_subset_1('#skF_2'(A_1891,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_4'('#skF_6','#skF_7'))
      | m1_subset_1('#skF_2'(A_1891,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1891))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1891)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_69082])).

tff(c_63817,plain,(
    ! [B_1597,B_24,A_23] :
      ( r2_hidden(B_1597,B_24)
      | ~ m1_subset_1(B_1597,A_23)
      | v1_xboole_0(A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_63789])).

tff(c_69946,plain,(
    ! [A_1891,B_24] :
      ( r2_hidden('#skF_2'(A_1891,'#skF_7','#skF_4'('#skF_6','#skF_7')),B_24)
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),B_24)
      | m1_subset_1('#skF_2'(A_1891,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1891))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1891)) ) ),
    inference(resolution,[status(thm)],[c_69940,c_63817])).

tff(c_70194,plain,(
    ! [A_1896,B_1897] :
      ( r2_hidden('#skF_2'(A_1896,'#skF_7','#skF_4'('#skF_6','#skF_7')),B_1897)
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),B_1897)
      | m1_subset_1('#skF_2'(A_1896,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1896))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1896)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_69946])).

tff(c_70252,plain,(
    ! [A_1896] :
      ( ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),'#skF_7')
      | m1_subset_1('#skF_2'(A_1896,'#skF_7','#skF_4'('#skF_6','#skF_7')),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1896))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1896)) ) ),
    inference(resolution,[status(thm)],[c_70194,c_572])).

tff(c_70484,plain,(
    ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70252])).

tff(c_72539,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_72533,c_70484])).

tff(c_72590,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_72539])).

tff(c_72592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_72590])).

tff(c_72594,plain,(
    r1_tarski('#skF_4'('#skF_6','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_70252])).

tff(c_62,plain,(
    ! [C_47,B_44,A_38] :
      ( C_47 = B_44
      | ~ r1_tarski(B_44,C_47)
      | ~ v2_tex_2(C_47,A_38)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v3_tex_2(B_44,A_38)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72615,plain,(
    ! [A_38] :
      ( '#skF_4'('#skF_6','#skF_7') = '#skF_7'
      | ~ v2_tex_2('#skF_7',A_38)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v3_tex_2('#skF_4'('#skF_6','#skF_7'),A_38)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_72594,c_62])).

tff(c_73897,plain,(
    ! [A_2011] :
      ( ~ v2_tex_2('#skF_7',A_2011)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_2011)))
      | ~ v3_tex_2('#skF_4'('#skF_6','#skF_7'),A_2011)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0(A_2011)))
      | ~ l1_pre_topc(A_2011) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_72615])).

tff(c_73907,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_73897])).

tff(c_73921,plain,
    ( ~ v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_404,c_399,c_1187,c_73907])).

tff(c_73922,plain,(
    ~ v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_73921])).

tff(c_112,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_131,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_112])).

tff(c_403,plain,(
    r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_131])).

tff(c_64201,plain,(
    ! [A_1625,B_1626] :
      ( v2_tex_2('#skF_4'(A_1625,B_1626),A_1625)
      | v3_tex_2(B_1626,A_1625)
      | ~ v2_tex_2(B_1626,A_1625)
      | ~ m1_subset_1(B_1626,k1_zfmisc_1(u1_struct_0(A_1625)))
      | ~ l1_pre_topc(A_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64230,plain,(
    ! [A_1625,A_23] :
      ( v2_tex_2('#skF_4'(A_1625,A_23),A_1625)
      | v3_tex_2(A_23,A_1625)
      | ~ v2_tex_2(A_23,A_1625)
      | ~ l1_pre_topc(A_1625)
      | ~ r1_tarski(A_23,u1_struct_0(A_1625)) ) ),
    inference(resolution,[status(thm)],[c_38,c_64201])).

tff(c_66833,plain,(
    ! [A_1779,A_1780] :
      ( r1_tarski(A_1779,'#skF_4'(A_1780,A_1779))
      | v3_tex_2(A_1779,A_1780)
      | ~ v2_tex_2(A_1779,A_1780)
      | ~ l1_pre_topc(A_1780)
      | ~ r1_tarski(A_1779,u1_struct_0(A_1780)) ) ),
    inference(resolution,[status(thm)],[c_38,c_64008])).

tff(c_66841,plain,(
    ! [A_1779] :
      ( r1_tarski(A_1779,'#skF_4'('#skF_6',A_1779))
      | v3_tex_2(A_1779,'#skF_6')
      | ~ v2_tex_2(A_1779,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r1_tarski(A_1779,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_66833])).

tff(c_66850,plain,(
    ! [A_1779] :
      ( r1_tarski(A_1779,'#skF_4'('#skF_6',A_1779))
      | v3_tex_2(A_1779,'#skF_6')
      | ~ v2_tex_2(A_1779,'#skF_6')
      | ~ r1_tarski(A_1779,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_66841])).

tff(c_63812,plain,(
    ! [B_1597,A_48] :
      ( r2_hidden(B_1597,A_48)
      | ~ m1_subset_1(B_1597,'#skF_5'(A_48))
      | v1_xboole_0('#skF_5'(A_48))
      | v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_72,c_63789])).

tff(c_68834,plain,(
    ! [B_1597] :
      ( r2_hidden(B_1597,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1597,'#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_5'('#skF_4'('#skF_6','#skF_7')))
      | v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68822,c_63812])).

tff(c_68872,plain,(
    ! [B_1597] :
      ( r2_hidden(B_1597,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1597,'#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68822,c_68834])).

tff(c_69151,plain,(
    ! [B_1872] :
      ( r2_hidden(B_1872,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1872,'#skF_4'('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_68816,c_64504,c_68872])).

tff(c_73937,plain,(
    ! [B_2012,B_2013] :
      ( m1_subset_1(B_2012,B_2013)
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),B_2013)
      | ~ m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_69151,c_574])).

tff(c_73947,plain,(
    ! [B_2012] :
      ( m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_7'))
      | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66850,c_73937])).

tff(c_73959,plain,(
    ! [B_2012] :
      ( m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_7'))
      | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72594,c_73947])).

tff(c_73960,plain,(
    ! [B_2012] :
      ( m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_2012,'#skF_4'('#skF_6','#skF_7'))
      | ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_73922,c_73959])).

tff(c_74034,plain,(
    ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_73960])).

tff(c_74037,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64230,c_74034])).

tff(c_74049,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_399,c_80,c_1187,c_74037])).

tff(c_74051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_74049])).

tff(c_74053,plain,(
    v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_73960])).

tff(c_56,plain,(
    ! [B_44,A_38] :
      ( r1_tarski(B_44,'#skF_4'(A_38,B_44))
      | v3_tex_2(B_44,A_38)
      | ~ v2_tex_2(B_44,A_38)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64381,plain,(
    ! [A_1640,B_1641] :
      ( r1_tarski('#skF_4'(A_1640,B_1641),'#skF_4'(A_1640,'#skF_4'(A_1640,B_1641)))
      | v3_tex_2('#skF_4'(A_1640,B_1641),A_1640)
      | ~ v2_tex_2('#skF_4'(A_1640,B_1641),A_1640)
      | v3_tex_2(B_1641,A_1640)
      | ~ v2_tex_2(B_1641,A_1640)
      | ~ m1_subset_1(B_1641,k1_zfmisc_1(u1_struct_0(A_1640)))
      | ~ l1_pre_topc(A_1640) ) ),
    inference(resolution,[status(thm)],[c_64334,c_56])).

tff(c_82287,plain,(
    ! [A_2203,B_2204] :
      ( r1_tarski('#skF_4'(A_2203,B_2204),'#skF_4'(A_2203,'#skF_4'(A_2203,B_2204)))
      | v3_tex_2('#skF_4'(A_2203,B_2204),A_2203)
      | ~ v2_tex_2('#skF_4'(A_2203,B_2204),A_2203)
      | v3_tex_2(B_2204,A_2203)
      | ~ v2_tex_2(B_2204,A_2203)
      | ~ m1_subset_1(B_2204,k1_zfmisc_1(u1_struct_0(A_2203)))
      | ~ l1_pre_topc(A_2203) ) ),
    inference(resolution,[status(thm)],[c_64334,c_56])).

tff(c_64514,plain,(
    ! [B_1647] :
      ( m1_subset_1(B_1647,'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1(B_1647,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_64499])).

tff(c_64516,plain,(
    ! [B_1647,B_24] :
      ( r2_hidden(B_1647,B_24)
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),B_24)
      | ~ m1_subset_1(B_1647,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64514,c_63817])).

tff(c_64522,plain,(
    ! [B_1647,B_24] :
      ( r2_hidden(B_1647,B_24)
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_7'),B_24)
      | ~ m1_subset_1(B_1647,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_64516])).

tff(c_82327,plain,(
    ! [B_1647] :
      ( r2_hidden(B_1647,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_1647,'#skF_7')
      | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | v3_tex_2('#skF_7','#skF_6')
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82287,c_64522])).

tff(c_82373,plain,(
    ! [B_1647] :
      ( r2_hidden(B_1647,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_1647,'#skF_7')
      | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
      | v3_tex_2('#skF_7','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_404,c_399,c_1187,c_74053,c_82327])).

tff(c_82381,plain,(
    ! [B_2205] :
      ( r2_hidden(B_2205,'#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1(B_2205,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_73922,c_82373])).

tff(c_82416,plain,(
    ! [B_24,B_2205] :
      ( ~ v1_xboole_0(B_24)
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),B_24)
      | ~ m1_subset_1(B_2205,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_82381,c_342])).

tff(c_82453,plain,(
    ! [B_2205] : ~ m1_subset_1(B_2205,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82416])).

tff(c_346,plain,(
    ! [A_10,A_92] :
      ( ~ v1_xboole_0(A_10)
      | ~ r2_hidden(A_92,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_325])).

tff(c_349,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_64837,plain,(
    ! [A_1667,B_1668] :
      ( r2_hidden('#skF_2'(A_1667,B_1668,k1_xboole_0),B_1668)
      | k1_xboole_0 = B_1668
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1667))
      | ~ m1_subset_1(B_1668,k1_zfmisc_1(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_64767,c_349])).

tff(c_65092,plain,(
    ! [A_1688,B_1689] :
      ( r2_hidden('#skF_2'(A_1688,B_1689,k1_xboole_0),B_1689)
      | k1_xboole_0 = B_1689
      | ~ m1_subset_1(B_1689,k1_zfmisc_1(A_1688)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_64837])).

tff(c_65123,plain,(
    ! [A_1688] :
      ( m1_subset_1('#skF_2'(A_1688,'#skF_7',k1_xboole_0),'#skF_7')
      | k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1688)) ) ),
    inference(resolution,[status(thm)],[c_65092,c_572])).

tff(c_65144,plain,(
    ! [A_1688] :
      ( m1_subset_1('#skF_2'(A_1688,'#skF_7',k1_xboole_0),'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1688)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_65123])).

tff(c_82466,plain,(
    ! [A_1688] : ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1688)) ),
    inference(negUnitSimplification,[status(thm)],[c_82453,c_65144])).

tff(c_82672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82466,c_404])).

tff(c_82674,plain,(
    ! [B_2209] :
      ( ~ v1_xboole_0(B_2209)
      | ~ r1_tarski('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),B_2209) ) ),
    inference(splitRight,[status(thm)],[c_82416])).

tff(c_82678,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7'))))
    | v3_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | ~ v2_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ v2_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64381,c_82674])).

tff(c_82697,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7'))))
    | v3_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | ~ v2_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | v3_tex_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_399,c_74053,c_82678])).

tff(c_82698,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7'))))
    | v3_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | ~ v2_tex_2('#skF_4'('#skF_6','#skF_4'('#skF_6','#skF_7')),'#skF_6')
    | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_73922,c_82697])).

tff(c_99973,plain,(
    ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_82698])).

tff(c_99982,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_64395,c_99973])).

tff(c_99995,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_99982])).

tff(c_99997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_99995])).

tff(c_99999,plain,(
    m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_82698])).

tff(c_65150,plain,(
    ! [A_1690] :
      ( m1_subset_1('#skF_2'(A_1690,'#skF_7',k1_xboole_0),'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1690)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_65123])).

tff(c_65152,plain,(
    ! [A_1690,B_24] :
      ( r2_hidden('#skF_2'(A_1690,'#skF_7',k1_xboole_0),B_24)
      | v1_xboole_0('#skF_7')
      | ~ r1_tarski('#skF_7',B_24)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1690)) ) ),
    inference(resolution,[status(thm)],[c_65150,c_63817])).

tff(c_65734,plain,(
    ! [A_1726,B_1727] :
      ( r2_hidden('#skF_2'(A_1726,'#skF_7',k1_xboole_0),B_1727)
      | ~ r1_tarski('#skF_7',B_1727)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1726)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_65152])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1(B_2,A_1)
      | ~ r2_hidden(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79023,plain,(
    ! [A_2130,B_2131] :
      ( m1_subset_1('#skF_2'(A_2130,'#skF_7',k1_xboole_0),B_2131)
      | v1_xboole_0(B_2131)
      | ~ r1_tarski('#skF_7',B_2131)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2130)) ) ),
    inference(resolution,[status(thm)],[c_65734,c_4])).

tff(c_14,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74091,plain,(
    ! [B_2023,A_2024] :
      ( r2_hidden(B_2023,A_2024)
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2024))
      | ~ m1_subset_1(B_2023,'#skF_4'('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_69151,c_14])).

tff(c_74102,plain,(
    ! [B_2023] :
      ( r2_hidden(B_2023,'#skF_7')
      | ~ m1_subset_1(B_2023,'#skF_4'('#skF_6','#skF_7'))
      | v3_tex_2('#skF_7','#skF_6')
      | ~ v2_tex_2('#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_64395,c_74091])).

tff(c_74119,plain,(
    ! [B_2023] :
      ( r2_hidden(B_2023,'#skF_7')
      | ~ m1_subset_1(B_2023,'#skF_4'('#skF_6','#skF_7'))
      | v3_tex_2('#skF_7','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_74102])).

tff(c_74120,plain,(
    ! [B_2023] :
      ( r2_hidden(B_2023,'#skF_7')
      | ~ m1_subset_1(B_2023,'#skF_4'('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_74119])).

tff(c_79045,plain,(
    ! [A_2130] :
      ( r2_hidden('#skF_2'(A_2130,'#skF_7',k1_xboole_0),'#skF_7')
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | ~ r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2130)) ) ),
    inference(resolution,[status(thm)],[c_79023,c_74120])).

tff(c_79246,plain,(
    ! [A_2130] :
      ( r2_hidden('#skF_2'(A_2130,'#skF_7',k1_xboole_0),'#skF_7')
      | ~ r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2130)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_79045])).

tff(c_79370,plain,(
    ~ r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_79246])).

tff(c_79373,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_66850,c_79370])).

tff(c_79379,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_1187,c_79373])).

tff(c_79381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_79379])).

tff(c_79383,plain,(
    r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_79246])).

tff(c_64858,plain,(
    ! [A_1667,B_1668,C_1669,A_4] :
      ( r2_hidden('#skF_2'(A_1667,B_1668,C_1669),A_4)
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_4))
      | r2_hidden('#skF_2'(A_1667,B_1668,C_1669),B_1668)
      | C_1669 = B_1668
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_1667))
      | ~ m1_subset_1(B_1668,k1_zfmisc_1(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_64767,c_14])).

tff(c_77997,plain,(
    ! [C_1669,B_1668,A_1667] :
      ( ~ m1_subset_1(C_1669,k1_zfmisc_1(B_1668))
      | C_1669 = B_1668
      | ~ m1_subset_1(C_1669,k1_zfmisc_1(A_1667))
      | ~ m1_subset_1(B_1668,k1_zfmisc_1(A_1667))
      | r2_hidden('#skF_2'(A_1667,B_1668,C_1669),B_1668) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_64858])).

tff(c_76083,plain,(
    ! [A_2064,B_2065,C_2066] :
      ( m1_subset_1('#skF_2'(A_2064,B_2065,C_2066),B_2065)
      | v1_xboole_0(B_2065)
      | r2_hidden('#skF_2'(A_2064,B_2065,C_2066),C_2066)
      | C_2066 = B_2065
      | ~ m1_subset_1(C_2066,k1_zfmisc_1(A_2064))
      | ~ m1_subset_1(B_2065,k1_zfmisc_1(A_2064)) ) ),
    inference(resolution,[status(thm)],[c_64767,c_4])).

tff(c_76098,plain,(
    ! [A_2064,C_2066] :
      ( r2_hidden('#skF_2'(A_2064,'#skF_4'('#skF_6','#skF_7'),C_2066),'#skF_7')
      | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
      | r2_hidden('#skF_2'(A_2064,'#skF_4'('#skF_6','#skF_7'),C_2066),C_2066)
      | C_2066 = '#skF_4'('#skF_6','#skF_7')
      | ~ m1_subset_1(C_2066,k1_zfmisc_1(A_2064))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2064)) ) ),
    inference(resolution,[status(thm)],[c_76083,c_74120])).

tff(c_76375,plain,(
    ! [A_2064,C_2066] :
      ( r2_hidden('#skF_2'(A_2064,'#skF_4'('#skF_6','#skF_7'),C_2066),'#skF_7')
      | r2_hidden('#skF_2'(A_2064,'#skF_4'('#skF_6','#skF_7'),C_2066),C_2066)
      | C_2066 = '#skF_4'('#skF_6','#skF_7')
      | ~ m1_subset_1(C_2066,k1_zfmisc_1(A_2064))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2064)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64504,c_76098])).

tff(c_100623,plain,(
    ! [A_2064] :
      ( '#skF_4'('#skF_6','#skF_7') = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2064))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2064))
      | r2_hidden('#skF_2'(A_2064,'#skF_4'('#skF_6','#skF_7'),'#skF_7'),'#skF_7') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_76375])).

tff(c_101147,plain,(
    ! [A_2572] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2572))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2572))
      | r2_hidden('#skF_2'(A_2572,'#skF_4'('#skF_6','#skF_7'),'#skF_7'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_100623])).

tff(c_26,plain,(
    ! [A_13,B_14,C_18] :
      ( ~ r2_hidden('#skF_2'(A_13,B_14,C_18),C_18)
      | ~ r2_hidden('#skF_2'(A_13,B_14,C_18),B_14)
      | C_18 = B_14
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_101149,plain,(
    ! [A_2572] :
      ( ~ r2_hidden('#skF_2'(A_2572,'#skF_4'('#skF_6','#skF_7'),'#skF_7'),'#skF_4'('#skF_6','#skF_7'))
      | '#skF_4'('#skF_6','#skF_7') = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2572))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2572)) ) ),
    inference(resolution,[status(thm)],[c_101147,c_26])).

tff(c_103026,plain,(
    ! [A_2604] :
      ( ~ r2_hidden('#skF_2'(A_2604,'#skF_4'('#skF_6','#skF_7'),'#skF_7'),'#skF_4'('#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2604))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2604)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_101149])).

tff(c_103034,plain,(
    ! [A_1667] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4'('#skF_6','#skF_7')))
      | '#skF_4'('#skF_6','#skF_7') = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1667))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_77997,c_103026])).

tff(c_103088,plain,(
    ! [A_1667] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4'('#skF_6','#skF_7')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1667))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_1667)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_103034])).

tff(c_103593,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_103088])).

tff(c_103602,plain,(
    ~ r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_103593])).

tff(c_103611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79383,c_103602])).

tff(c_104886,plain,(
    ! [A_2631] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_2631))
      | ~ m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(A_2631)) ) ),
    inference(splitRight,[status(thm)],[c_103088])).

tff(c_104897,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_99999,c_104886])).

tff(c_104936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_104897])).

tff(c_104938,plain,(
    v1_zfmisc_1('#skF_4'('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68773])).

tff(c_1384,plain,(
    ! [A_185,B_186] :
      ( '#skF_4'(A_185,B_186) != B_186
      | v3_tex_2(B_186,A_185)
      | ~ v2_tex_2(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1399,plain,(
    ! [B_186] :
      ( '#skF_4'('#skF_6',B_186) != B_186
      | v3_tex_2(B_186,'#skF_6')
      | ~ v2_tex_2(B_186,'#skF_6')
      | ~ m1_subset_1(B_186,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1384])).

tff(c_1868,plain,(
    ! [B_228] :
      ( '#skF_4'('#skF_6',B_228) != B_228
      | v3_tex_2(B_228,'#skF_6')
      | ~ v2_tex_2(B_228,'#skF_6')
      | ~ m1_subset_1(B_228,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1399])).

tff(c_1883,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_404,c_1868])).

tff(c_1905,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1883])).

tff(c_1906,plain,(
    '#skF_4'('#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1905])).

tff(c_1806,plain,(
    ! [B_222,A_223] :
      ( r1_tarski(B_222,'#skF_4'(A_223,B_222))
      | v3_tex_2(B_222,A_223)
      | ~ v2_tex_2(B_222,A_223)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1817,plain,(
    ! [B_222] :
      ( r1_tarski(B_222,'#skF_4'('#skF_6',B_222))
      | v3_tex_2(B_222,'#skF_6')
      | ~ v2_tex_2(B_222,'#skF_6')
      | ~ m1_subset_1(B_222,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1806])).

tff(c_4297,plain,(
    ! [B_373] :
      ( r1_tarski(B_373,'#skF_4'('#skF_6',B_373))
      | v3_tex_2(B_373,'#skF_6')
      | ~ v2_tex_2(B_373,'#skF_6')
      | ~ m1_subset_1(B_373,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1817])).

tff(c_1327,plain,(
    ! [B_181,A_182,A_183] :
      ( r2_hidden(B_181,A_182)
      | ~ m1_subset_1(A_183,k1_zfmisc_1(A_182))
      | ~ m1_subset_1(B_181,A_183)
      | v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_6,c_741])).

tff(c_1336,plain,(
    ! [B_181] :
      ( r2_hidden(B_181,'#skF_7')
      | ~ m1_subset_1(B_181,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_404,c_1327])).

tff(c_1360,plain,(
    ! [B_184] :
      ( r2_hidden(B_184,'#skF_7')
      | ~ m1_subset_1(B_184,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_1336])).

tff(c_1378,plain,(
    ! [B_24,B_184] :
      ( ~ v1_xboole_0(B_24)
      | ~ r1_tarski('#skF_7',B_24)
      | ~ m1_subset_1(B_184,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1360,c_342])).

tff(c_1428,plain,(
    ! [B_189] : ~ m1_subset_1(B_189,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_1446,plain,(
    ! [C_191,B_192] :
      ( C_191 = B_192
      | ~ m1_subset_1(C_191,k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1(B_192,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_24,c_1428])).

tff(c_1510,plain,(
    ! [B_195] :
      ( k1_xboole_0 = B_195
      | ~ m1_subset_1(B_195,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_20,c_1446])).

tff(c_1525,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_404,c_1510])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_873,c_1525])).

tff(c_1548,plain,(
    ! [B_24] :
      ( ~ v1_xboole_0(B_24)
      | ~ r1_tarski('#skF_7',B_24) ) ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_4371,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4297,c_1548])).

tff(c_4408,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_1187,c_4371])).

tff(c_4409,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_4408])).

tff(c_1164,plain,
    ( v2_tex_2('#skF_5'('#skF_7'),'#skF_6')
    | v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_1152])).

tff(c_1186,plain,
    ( v2_tex_2('#skF_5'('#skF_7'),'#skF_6')
    | v1_zfmisc_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_1164])).

tff(c_1192,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_1966,plain,(
    ! [A_231,B_232] :
      ( m1_subset_1('#skF_4'(A_231,B_232),k1_zfmisc_1(u1_struct_0(A_231)))
      | v3_tex_2(B_232,A_231)
      | ~ v2_tex_2(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_61680,plain,(
    ! [A_1511,B_1512] :
      ( r1_tarski('#skF_4'(A_1511,B_1512),u1_struct_0(A_1511))
      | v3_tex_2(B_1512,A_1511)
      | ~ v2_tex_2(B_1512,A_1511)
      | ~ m1_subset_1(B_1512,k1_zfmisc_1(u1_struct_0(A_1511)))
      | ~ l1_pre_topc(A_1511) ) ),
    inference(resolution,[status(thm)],[c_1966,c_36])).

tff(c_61734,plain,(
    ! [B_1512] :
      ( r1_tarski('#skF_4'('#skF_6',B_1512),'#skF_7')
      | v3_tex_2(B_1512,'#skF_6')
      | ~ v2_tex_2(B_1512,'#skF_6')
      | ~ m1_subset_1(B_1512,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_61680])).

tff(c_62035,plain,(
    ! [B_1524] :
      ( r1_tarski('#skF_4'('#skF_6',B_1524),'#skF_7')
      | v3_tex_2(B_1524,'#skF_6')
      | ~ v2_tex_2(B_1524,'#skF_6')
      | ~ m1_subset_1(B_1524,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_399,c_61734])).

tff(c_394,plain,(
    ! [A_23,B_24] :
      ( v1_subset_1(A_23,B_24)
      | B_24 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_38,c_370])).

tff(c_2084,plain,(
    ! [A_240,B_241] :
      ( ~ v1_subset_1(A_240,B_241)
      | v1_xboole_0(A_240)
      | ~ v1_zfmisc_1(B_241)
      | v1_xboole_0(B_241)
      | ~ r1_tarski(A_240,B_241) ) ),
    inference(resolution,[status(thm)],[c_38,c_785])).

tff(c_2106,plain,(
    ! [A_23,B_24] :
      ( v1_xboole_0(A_23)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | B_24 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_394,c_2084])).

tff(c_62059,plain,(
    ! [B_1524] :
      ( v1_xboole_0('#skF_4'('#skF_6',B_1524))
      | ~ v1_zfmisc_1('#skF_7')
      | v1_xboole_0('#skF_7')
      | '#skF_4'('#skF_6',B_1524) = '#skF_7'
      | v3_tex_2(B_1524,'#skF_6')
      | ~ v2_tex_2(B_1524,'#skF_6')
      | ~ m1_subset_1(B_1524,k1_zfmisc_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_62035,c_2106])).

tff(c_62087,plain,(
    ! [B_1524] :
      ( v1_xboole_0('#skF_4'('#skF_6',B_1524))
      | v1_xboole_0('#skF_7')
      | '#skF_4'('#skF_6',B_1524) = '#skF_7'
      | v3_tex_2(B_1524,'#skF_6')
      | ~ v2_tex_2(B_1524,'#skF_6')
      | ~ m1_subset_1(B_1524,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_62059])).

tff(c_63454,plain,(
    ! [B_1575] :
      ( v1_xboole_0('#skF_4'('#skF_6',B_1575))
      | '#skF_4'('#skF_6',B_1575) = '#skF_7'
      | v3_tex_2(B_1575,'#skF_6')
      | ~ v2_tex_2(B_1575,'#skF_6')
      | ~ m1_subset_1(B_1575,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_62087])).

tff(c_63488,plain,
    ( v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | '#skF_4'('#skF_6','#skF_7') = '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_404,c_63454])).

tff(c_63523,plain,
    ( v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | '#skF_4'('#skF_6','#skF_7') = '#skF_7'
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_63488])).

tff(c_63525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1906,c_4409,c_63523])).

tff(c_63527,plain,(
    ~ v1_zfmisc_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_63530,plain,
    ( '#skF_5'('#skF_7') = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1085,c_63527])).

tff(c_63533,plain,(
    '#skF_5'('#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_63530])).

tff(c_114473,plain,(
    ! [A_2845] :
      ( r1_tarski('#skF_5'(u1_struct_0(A_2845)),'#skF_4'(A_2845,'#skF_5'(u1_struct_0(A_2845))))
      | v3_tex_2('#skF_5'(u1_struct_0(A_2845)),A_2845)
      | ~ v2_tex_2('#skF_5'(u1_struct_0(A_2845)),A_2845)
      | ~ l1_pre_topc(A_2845)
      | v1_zfmisc_1(u1_struct_0(A_2845))
      | v1_xboole_0(u1_struct_0(A_2845)) ) ),
    inference(resolution,[status(thm)],[c_72,c_64008])).

tff(c_114519,plain,
    ( r1_tarski('#skF_5'('#skF_7'),'#skF_4'('#skF_6','#skF_5'(u1_struct_0('#skF_6'))))
    | v3_tex_2('#skF_5'(u1_struct_0('#skF_6')),'#skF_6')
    | ~ v2_tex_2('#skF_5'(u1_struct_0('#skF_6')),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | v1_zfmisc_1(u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_114473])).

tff(c_114543,plain,
    ( r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_399,c_80,c_1187,c_63533,c_399,c_63533,c_399,c_63533,c_399,c_63533,c_114519])).

tff(c_114544,plain,(
    r1_tarski('#skF_7','#skF_4'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_63527,c_135,c_114543])).

tff(c_63700,plain,(
    ! [A_1591,B_1592] :
      ( ~ v1_subset_1(A_1591,B_1592)
      | v1_xboole_0(A_1591)
      | ~ v1_zfmisc_1(B_1592)
      | v1_xboole_0(B_1592)
      | ~ r1_tarski(A_1591,B_1592) ) ),
    inference(resolution,[status(thm)],[c_38,c_785])).

tff(c_63722,plain,(
    ! [A_23,B_24] :
      ( v1_xboole_0(A_23)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | B_24 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_394,c_63700])).

tff(c_114616,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_4'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | '#skF_4'('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_114544,c_63722])).

tff(c_114667,plain,
    ( v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | '#skF_4'('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104938,c_114616])).

tff(c_114669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64141,c_64504,c_401,c_114667])).

tff(c_114719,plain,(
    ! [B_2848] :
      ( v1_xboole_0(k1_tarski(B_2848))
      | ~ v1_xboole_0(B_2848) ) ),
    inference(splitRight,[status(thm)],[c_777])).

tff(c_2,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ~ v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_114722,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_114719,c_99])).

tff(c_114726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_114722])).

tff(c_114728,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_612])).

tff(c_114731,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_114728])).

tff(c_114735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_114731])).

tff(c_114736,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_115169,plain,(
    ! [B_2892,A_2893] :
      ( m1_subset_1(k1_tarski(B_2892),k1_zfmisc_1(A_2893))
      | k1_xboole_0 = A_2893
      | ~ m1_subset_1(B_2892,A_2893) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115212,plain,(
    ! [B_2896,A_2897] :
      ( v1_xboole_0(k1_tarski(B_2896))
      | ~ v1_xboole_0(A_2897)
      | k1_xboole_0 = A_2897
      | ~ m1_subset_1(B_2896,A_2897) ) ),
    inference(resolution,[status(thm)],[c_115169,c_34])).

tff(c_115241,plain,(
    ! [B_2,A_1] :
      ( v1_xboole_0(k1_tarski(B_2))
      | k1_xboole_0 = A_1
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_115212])).

tff(c_115249,plain,(
    ! [A_2898] :
      ( k1_xboole_0 = A_2898
      | ~ v1_xboole_0(A_2898) ) ),
    inference(splitLeft,[status(thm)],[c_115241])).

tff(c_115262,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_114736,c_115249])).

tff(c_103,plain,(
    ! [A_59] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_115325,plain,(
    m1_subset_1('#skF_7',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115262,c_115262,c_105])).

tff(c_115328,plain,(
    k1_zfmisc_1('#skF_7') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115262,c_115262,c_2])).

tff(c_114795,plain,(
    ! [B_2854,A_2855] :
      ( v1_subset_1(B_2854,A_2855)
      | B_2854 = A_2855
      | ~ m1_subset_1(B_2854,k1_zfmisc_1(A_2855)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_114811,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_114795])).

tff(c_114824,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_114811])).

tff(c_115468,plain,(
    ! [B_2906,A_2907] :
      ( v2_tex_2(B_2906,A_2907)
      | ~ m1_subset_1(B_2906,k1_zfmisc_1(u1_struct_0(A_2907)))
      | ~ l1_pre_topc(A_2907)
      | ~ v1_tdlat_3(A_2907)
      | ~ v2_pre_topc(A_2907)
      | v2_struct_0(A_2907) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_115479,plain,(
    ! [B_2906] :
      ( v2_tex_2(B_2906,'#skF_6')
      | ~ m1_subset_1(B_2906,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v1_tdlat_3('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114824,c_115468])).

tff(c_115494,plain,(
    ! [B_2906] :
      ( v2_tex_2(B_2906,'#skF_6')
      | ~ m1_subset_1(B_2906,k1_tarski('#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_115328,c_115479])).

tff(c_115511,plain,(
    ! [B_2909] :
      ( v2_tex_2(B_2909,'#skF_6')
      | ~ m1_subset_1(B_2909,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_115494])).

tff(c_115519,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_115325,c_115511])).

tff(c_115737,plain,(
    ! [A_2931,B_2932] :
      ( '#skF_4'(A_2931,B_2932) != B_2932
      | v3_tex_2(B_2932,A_2931)
      | ~ v2_tex_2(B_2932,A_2931)
      | ~ m1_subset_1(B_2932,k1_zfmisc_1(u1_struct_0(A_2931)))
      | ~ l1_pre_topc(A_2931) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_115752,plain,(
    ! [B_2932] :
      ( '#skF_4'('#skF_6',B_2932) != B_2932
      | v3_tex_2(B_2932,'#skF_6')
      | ~ v2_tex_2(B_2932,'#skF_6')
      | ~ m1_subset_1(B_2932,k1_zfmisc_1('#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114824,c_115737])).

tff(c_115921,plain,(
    ! [B_2948] :
      ( '#skF_4'('#skF_6',B_2948) != B_2948
      | v3_tex_2(B_2948,'#skF_6')
      | ~ v2_tex_2(B_2948,'#skF_6')
      | ~ m1_subset_1(B_2948,k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_115328,c_115752])).

tff(c_115931,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_115325,c_115921])).

tff(c_115940,plain,
    ( '#skF_4'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115519,c_115931])).

tff(c_115941,plain,(
    '#skF_4'('#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_115940])).

tff(c_116117,plain,(
    ! [A_2971,B_2972] :
      ( m1_subset_1('#skF_4'(A_2971,B_2972),k1_zfmisc_1(u1_struct_0(A_2971)))
      | v3_tex_2(B_2972,A_2971)
      | ~ v2_tex_2(B_2972,A_2971)
      | ~ m1_subset_1(B_2972,k1_zfmisc_1(u1_struct_0(A_2971)))
      | ~ l1_pre_topc(A_2971) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_116159,plain,(
    ! [B_2972] :
      ( m1_subset_1('#skF_4'('#skF_6',B_2972),k1_zfmisc_1('#skF_7'))
      | v3_tex_2(B_2972,'#skF_6')
      | ~ v2_tex_2(B_2972,'#skF_6')
      | ~ m1_subset_1(B_2972,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114824,c_116117])).

tff(c_116386,plain,(
    ! [B_2995] :
      ( m1_subset_1('#skF_4'('#skF_6',B_2995),k1_tarski('#skF_7'))
      | v3_tex_2(B_2995,'#skF_6')
      | ~ v2_tex_2(B_2995,'#skF_6')
      | ~ m1_subset_1(B_2995,k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_115328,c_114824,c_115328,c_116159])).

tff(c_263,plain,(
    ! [B_84] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_tarski(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_114761,plain,(
    ! [B_84] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_tarski(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_263])).

tff(c_115318,plain,(
    ! [B_84] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115262,c_114761])).

tff(c_117329,plain,(
    ! [B_3065] :
      ( v1_xboole_0('#skF_4'('#skF_6',B_3065))
      | v3_tex_2(B_3065,'#skF_6')
      | ~ v2_tex_2(B_3065,'#skF_6')
      | ~ m1_subset_1(B_3065,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_116386,c_115318])).

tff(c_117342,plain,
    ( v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_115325,c_117329])).

tff(c_117352,plain,
    ( v1_xboole_0('#skF_4'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115519,c_117342])).

tff(c_117353,plain,(
    v1_xboole_0('#skF_4'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_117352])).

tff(c_115248,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(splitLeft,[status(thm)],[c_115241])).

tff(c_115308,plain,(
    ! [A_1] :
      ( A_1 = '#skF_7'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115262,c_115248])).

tff(c_117357,plain,(
    '#skF_4'('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_117353,c_115308])).

tff(c_117361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115941,c_117357])).

tff(c_117404,plain,(
    ! [B_3068] :
      ( v1_xboole_0(k1_tarski(B_3068))
      | ~ v1_xboole_0(B_3068) ) ),
    inference(splitRight,[status(thm)],[c_115241])).

tff(c_117407,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_117404,c_99])).

tff(c_117411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_117407])).

tff(c_117413,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_118246,plain,(
    ! [B_3153,A_3154] :
      ( ~ v3_tex_2(B_3153,A_3154)
      | ~ m1_subset_1(B_3153,k1_zfmisc_1(u1_struct_0(A_3154)))
      | ~ v1_xboole_0(B_3153)
      | ~ l1_pre_topc(A_3154)
      | ~ v2_pre_topc(A_3154)
      | v2_struct_0(A_3154) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_118272,plain,
    ( ~ v3_tex_2('#skF_7','#skF_6')
    | ~ v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_118246])).

tff(c_118285,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_117413,c_118272])).

tff(c_118286,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_118285])).

tff(c_117549,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_117521])).

tff(c_117563,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_117549])).

tff(c_117412,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_117955,plain,(
    ! [B_3136,A_3137] :
      ( ~ v1_subset_1(B_3136,A_3137)
      | v1_xboole_0(B_3136)
      | ~ m1_subset_1(B_3136,k1_zfmisc_1(A_3137))
      | ~ v1_zfmisc_1(A_3137)
      | v1_xboole_0(A_3137) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_117977,plain,
    ( ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1(u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_117955])).

tff(c_117993,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1(u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117412,c_117977])).

tff(c_117994,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1(u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_117563,c_117993])).

tff(c_118017,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_117994])).

tff(c_117688,plain,(
    ! [A_3103] :
      ( m1_subset_1('#skF_5'(A_3103),k1_zfmisc_1(A_3103))
      | v1_zfmisc_1(A_3103)
      | v1_xboole_0(A_3103) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_118201,plain,(
    ! [A_3151] :
      ( v1_subset_1('#skF_5'(A_3151),A_3151)
      | '#skF_5'(A_3151) = A_3151
      | v1_zfmisc_1(A_3151)
      | v1_xboole_0(A_3151) ) ),
    inference(resolution,[status(thm)],[c_117688,c_50])).

tff(c_118206,plain,(
    ! [A_3152] :
      ( '#skF_5'(A_3152) = A_3152
      | v1_zfmisc_1(A_3152)
      | v1_xboole_0(A_3152) ) ),
    inference(resolution,[status(thm)],[c_118201,c_66])).

tff(c_118209,plain,
    ( '#skF_5'(u1_struct_0('#skF_6')) = u1_struct_0('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_118206,c_118017])).

tff(c_118215,plain,(
    '#skF_5'(u1_struct_0('#skF_6')) = u1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_117563,c_118209])).

tff(c_118223,plain,
    ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_zfmisc_1(u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118215,c_72])).

tff(c_118236,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_117563,c_118017,c_118223])).

tff(c_74,plain,(
    ! [B_52,A_50] :
      ( v2_tex_2(B_52,A_50)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v1_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_118302,plain,
    ( v2_tex_2(u1_struct_0('#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v1_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_118236,c_74])).

tff(c_118334,plain,
    ( v2_tex_2(u1_struct_0('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_118302])).

tff(c_118335,plain,(
    v2_tex_2(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_118334])).

tff(c_119650,plain,(
    ! [C_3252,B_3253,A_3254] :
      ( C_3252 = B_3253
      | ~ r1_tarski(B_3253,C_3252)
      | ~ v2_tex_2(C_3252,A_3254)
      | ~ m1_subset_1(C_3252,k1_zfmisc_1(u1_struct_0(A_3254)))
      | ~ v3_tex_2(B_3253,A_3254)
      | ~ m1_subset_1(B_3253,k1_zfmisc_1(u1_struct_0(A_3254)))
      | ~ l1_pre_topc(A_3254) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_119668,plain,(
    ! [A_3254] :
      ( u1_struct_0('#skF_6') = '#skF_7'
      | ~ v2_tex_2(u1_struct_0('#skF_6'),A_3254)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_3254)))
      | ~ v3_tex_2('#skF_7',A_3254)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3254)))
      | ~ l1_pre_topc(A_3254) ) ),
    inference(resolution,[status(thm)],[c_131,c_119650])).

tff(c_119992,plain,(
    ! [A_3288] :
      ( ~ v2_tex_2(u1_struct_0('#skF_6'),A_3288)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_3288)))
      | ~ v3_tex_2('#skF_7',A_3288)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_3288)))
      | ~ l1_pre_topc(A_3288) ) ),
    inference(splitLeft,[status(thm)],[c_119668])).

tff(c_119995,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_6'),'#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_118236,c_119992])).

tff(c_120005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_117413,c_118335,c_119995])).

tff(c_120006,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_119668])).

tff(c_120025,plain,(
    ~ v1_zfmisc_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120006,c_118017])).

tff(c_120028,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120006,c_117412])).

tff(c_118205,plain,(
    ! [A_3151] :
      ( '#skF_5'(A_3151) = A_3151
      | v1_zfmisc_1(A_3151)
      | v1_xboole_0(A_3151) ) ),
    inference(resolution,[status(thm)],[c_118201,c_66])).

tff(c_120094,plain,
    ( '#skF_5'('#skF_7') = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_118205,c_120025])).

tff(c_120097,plain,(
    '#skF_5'('#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_118286,c_120094])).

tff(c_120138,plain,
    ( ~ v1_subset_1('#skF_7','#skF_7')
    | v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_120097,c_66])).

tff(c_120152,plain,
    ( v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120028,c_120138])).

tff(c_120154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118286,c_120025,c_120152])).

tff(c_120155,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_117994])).

tff(c_120250,plain,(
    ! [B_3294,A_3295] :
      ( ~ v3_tex_2(B_3294,A_3295)
      | ~ m1_subset_1(B_3294,k1_zfmisc_1(u1_struct_0(A_3295)))
      | ~ v1_xboole_0(B_3294)
      | ~ l1_pre_topc(A_3295)
      | ~ v2_pre_topc(A_3295)
      | v2_struct_0(A_3295) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_120268,plain,
    ( ~ v3_tex_2('#skF_7','#skF_6')
    | ~ v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_120250])).

tff(c_120275,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_120155,c_117413,c_120268])).

tff(c_120277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_120275])).

tff(c_120278,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_117549])).

tff(c_120508,plain,(
    ! [B_3321,A_3322] :
      ( m1_subset_1(k1_tarski(B_3321),k1_zfmisc_1(A_3322))
      | k1_xboole_0 = A_3322
      | ~ m1_subset_1(B_3321,A_3322) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120623,plain,(
    ! [B_3341,A_3342] :
      ( v1_xboole_0(k1_tarski(B_3341))
      | ~ v1_xboole_0(A_3342)
      | k1_xboole_0 = A_3342
      | ~ m1_subset_1(B_3341,A_3342) ) ),
    inference(resolution,[status(thm)],[c_120508,c_34])).

tff(c_120651,plain,(
    ! [B_2,A_1] :
      ( v1_xboole_0(k1_tarski(B_2))
      | k1_xboole_0 = A_1
      | ~ v1_xboole_0(B_2)
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_120623])).

tff(c_120702,plain,(
    ! [A_3345] :
      ( k1_xboole_0 = A_3345
      | ~ v1_xboole_0(A_3345) ) ),
    inference(splitLeft,[status(thm)],[c_120651])).

tff(c_120719,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_120278,c_120702])).

tff(c_117457,plain,(
    ! [B_3075] :
      ( ~ v1_subset_1(B_3075,B_3075)
      | ~ m1_subset_1(B_3075,k1_zfmisc_1(B_3075)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_117475,plain,(
    ~ v1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_117457])).

tff(c_120738,plain,(
    ~ v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120719,c_120719,c_117475])).

tff(c_120279,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_117549])).

tff(c_120718,plain,(
    u1_struct_0('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120279,c_120702])).

tff(c_120750,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120719,c_120718])).

tff(c_120752,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120750,c_117412])).

tff(c_120798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120738,c_120752])).

tff(c_120841,plain,(
    ! [B_3350] :
      ( v1_xboole_0(k1_tarski(B_3350))
      | ~ v1_xboole_0(B_3350) ) ),
    inference(splitRight,[status(thm)],[c_120651])).

tff(c_120844,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_120841,c_99])).

tff(c_120848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117562,c_120844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.16/21.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.65/21.26  
% 30.65/21.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.65/21.26  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 30.65/21.26  
% 30.65/21.26  %Foreground sorts:
% 30.65/21.26  
% 30.65/21.26  
% 30.65/21.26  %Background operators:
% 30.65/21.26  
% 30.65/21.26  
% 30.65/21.26  %Foreground operators:
% 30.65/21.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 30.65/21.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 30.65/21.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.65/21.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.65/21.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 30.65/21.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 30.65/21.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 30.65/21.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.65/21.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 30.65/21.26  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 30.65/21.26  tff('#skF_7', type, '#skF_7': $i).
% 30.65/21.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.65/21.26  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 30.65/21.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 30.65/21.26  tff('#skF_6', type, '#skF_6': $i).
% 30.65/21.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.65/21.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.65/21.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.65/21.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 30.65/21.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.65/21.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 30.65/21.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 30.65/21.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 30.65/21.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.65/21.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 30.65/21.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.65/21.26  
% 30.86/21.31  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 30.86/21.31  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 30.86/21.31  tff(f_54, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 30.86/21.31  tff(f_212, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 30.86/21.31  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 30.86/21.31  tff(f_129, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 30.86/21.31  tff(f_179, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 30.86/21.31  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 30.86/21.31  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 30.86/21.31  tff(f_94, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 30.86/21.31  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 30.86/21.31  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 30.86/21.31  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 30.86/21.31  tff(f_88, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 30.86/21.31  tff(f_101, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 30.86/21.31  tff(f_122, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 30.86/21.31  tff(f_165, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B)) & ~v1_zfmisc_1(B)) & ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tex_2)).
% 30.86/21.31  tff(f_26, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 30.86/21.31  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 30.86/21.31  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 30.86/21.31  tff(c_20, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.86/21.31  tff(c_117521, plain, (![B_3086, A_3087]: (v1_xboole_0(B_3086) | ~m1_subset_1(B_3086, k1_zfmisc_1(A_3087)) | ~v1_xboole_0(A_3087))), inference(cnfTransformation, [status(thm)], [f_84])).
% 30.86/21.31  tff(c_117550, plain, (![A_10]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_20, c_117521])).
% 30.86/21.31  tff(c_117551, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitLeft, [status(thm)], [c_117550])).
% 30.86/21.31  tff(c_16, plain, (![A_8]: (v1_xboole_0('#skF_1'(A_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 30.86/21.31  tff(c_117561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117551, c_16])).
% 30.86/21.31  tff(c_117562, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_117550])).
% 30.86/21.31  tff(c_86, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_84, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_241, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 30.86/21.31  tff(c_270, plain, (![A_10]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_20, c_241])).
% 30.86/21.31  tff(c_271, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitLeft, [status(thm)], [c_270])).
% 30.86/21.31  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_16])).
% 30.86/21.31  tff(c_281, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_270])).
% 30.86/21.31  tff(c_88, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v3_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_135, plain, (~v3_tex_2('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_88])).
% 30.86/21.31  tff(c_44, plain, (![A_31]: (v1_xboole_0('#skF_3'(A_31)) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.86/21.31  tff(c_94, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_197, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_135, c_94])).
% 30.86/21.31  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_370, plain, (![B_95, A_96]: (v1_subset_1(B_95, A_96) | B_95=A_96 | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 30.86/21.31  tff(c_386, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_370])).
% 30.86/21.31  tff(c_399, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_197, c_386])).
% 30.86/21.31  tff(c_404, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_399, c_78])).
% 30.86/21.31  tff(c_82, plain, (v1_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 30.86/21.31  tff(c_1111, plain, (![B_162, A_163]: (v2_tex_2(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v1_tdlat_3(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_179])).
% 30.86/21.31  tff(c_1126, plain, (![B_162]: (v2_tex_2(B_162, '#skF_6') | ~m1_subset_1(B_162, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1111])).
% 30.86/21.31  tff(c_1146, plain, (![B_162]: (v2_tex_2(B_162, '#skF_6') | ~m1_subset_1(B_162, k1_zfmisc_1('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1126])).
% 30.86/21.31  tff(c_1152, plain, (![B_164]: (v2_tex_2(B_164, '#skF_6') | ~m1_subset_1(B_164, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1146])).
% 30.86/21.31  tff(c_1187, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_404, c_1152])).
% 30.86/21.31  tff(c_63726, plain, (![A_1593, B_1594]: ('#skF_4'(A_1593, B_1594)!=B_1594 | v3_tex_2(B_1594, A_1593) | ~v2_tex_2(B_1594, A_1593) | ~m1_subset_1(B_1594, k1_zfmisc_1(u1_struct_0(A_1593))) | ~l1_pre_topc(A_1593))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_63741, plain, (![B_1594]: ('#skF_4'('#skF_6', B_1594)!=B_1594 | v3_tex_2(B_1594, '#skF_6') | ~v2_tex_2(B_1594, '#skF_6') | ~m1_subset_1(B_1594, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_63726])).
% 30.86/21.31  tff(c_64102, plain, (![B_1620]: ('#skF_4'('#skF_6', B_1620)!=B_1620 | v3_tex_2(B_1620, '#skF_6') | ~v2_tex_2(B_1620, '#skF_6') | ~m1_subset_1(B_1620, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_63741])).
% 30.86/21.31  tff(c_64117, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_404, c_64102])).
% 30.86/21.31  tff(c_64140, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_64117])).
% 30.86/21.31  tff(c_64141, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_135, c_64140])).
% 30.86/21.31  tff(c_64008, plain, (![B_1615, A_1616]: (r1_tarski(B_1615, '#skF_4'(A_1616, B_1615)) | v3_tex_2(B_1615, A_1616) | ~v2_tex_2(B_1615, A_1616) | ~m1_subset_1(B_1615, k1_zfmisc_1(u1_struct_0(A_1616))) | ~l1_pre_topc(A_1616))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_64019, plain, (![B_1615]: (r1_tarski(B_1615, '#skF_4'('#skF_6', B_1615)) | v3_tex_2(B_1615, '#skF_6') | ~v2_tex_2(B_1615, '#skF_6') | ~m1_subset_1(B_1615, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_64008])).
% 30.86/21.31  tff(c_64449, plain, (![B_1646]: (r1_tarski(B_1646, '#skF_4'('#skF_6', B_1646)) | v3_tex_2(B_1646, '#skF_6') | ~v2_tex_2(B_1646, '#skF_6') | ~m1_subset_1(B_1646, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64019])).
% 30.86/21.31  tff(c_6, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.86/21.31  tff(c_46, plain, (![A_31]: (m1_subset_1('#skF_3'(A_31), k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 30.86/21.31  tff(c_411, plain, (m1_subset_1('#skF_3'('#skF_6'), k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_399, c_46])).
% 30.86/21.31  tff(c_417, plain, (m1_subset_1('#skF_3'('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_411])).
% 30.86/21.31  tff(c_550, plain, (![A_102, C_103, B_104]: (m1_subset_1(A_102, C_103) | ~m1_subset_1(B_104, k1_zfmisc_1(C_103)) | ~r2_hidden(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_94])).
% 30.86/21.31  tff(c_607, plain, (![A_109]: (m1_subset_1(A_109, '#skF_7') | ~r2_hidden(A_109, '#skF_3'('#skF_6')))), inference(resolution, [status(thm)], [c_417, c_550])).
% 30.86/21.31  tff(c_612, plain, (![B_2]: (m1_subset_1(B_2, '#skF_7') | ~m1_subset_1(B_2, '#skF_3'('#skF_6')) | v1_xboole_0('#skF_3'('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_607])).
% 30.86/21.31  tff(c_729, plain, (v1_xboole_0('#skF_3'('#skF_6'))), inference(splitLeft, [status(thm)], [c_612])).
% 30.86/21.31  tff(c_8, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~v1_xboole_0(B_2) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.86/21.31  tff(c_666, plain, (![B_120, A_121]: (m1_subset_1(k1_tarski(B_120), k1_zfmisc_1(A_121)) | k1_xboole_0=A_121 | ~m1_subset_1(B_120, A_121))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.86/21.31  tff(c_34, plain, (![B_22, A_20]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 30.86/21.31  tff(c_745, plain, (![B_133, A_134]: (v1_xboole_0(k1_tarski(B_133)) | ~v1_xboole_0(A_134) | k1_xboole_0=A_134 | ~m1_subset_1(B_133, A_134))), inference(resolution, [status(thm)], [c_666, c_34])).
% 30.86/21.31  tff(c_777, plain, (![B_2, A_1]: (v1_xboole_0(k1_tarski(B_2)) | k1_xboole_0=A_1 | ~v1_xboole_0(B_2) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_8, c_745])).
% 30.86/21.31  tff(c_833, plain, (![A_137]: (k1_xboole_0=A_137 | ~v1_xboole_0(A_137))), inference(splitLeft, [status(thm)], [c_777])).
% 30.86/21.31  tff(c_846, plain, ('#skF_3'('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_729, c_833])).
% 30.86/21.31  tff(c_269, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_241])).
% 30.86/21.31  tff(c_282, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_269])).
% 30.86/21.31  tff(c_401, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_282])).
% 30.86/21.31  tff(c_50, plain, (![B_37, A_36]: (v1_subset_1(B_37, A_36) | B_37=A_36 | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 30.86/21.31  tff(c_509, plain, (v1_subset_1('#skF_3'('#skF_6'), '#skF_7') | '#skF_3'('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_417, c_50])).
% 30.86/21.31  tff(c_515, plain, ('#skF_3'('#skF_6')='#skF_7'), inference(splitLeft, [status(thm)], [c_509])).
% 30.86/21.31  tff(c_529, plain, (v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_515, c_44])).
% 30.86/21.31  tff(c_537, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_529])).
% 30.86/21.31  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_537])).
% 30.86/21.31  tff(c_541, plain, ('#skF_3'('#skF_6')!='#skF_7'), inference(splitRight, [status(thm)], [c_509])).
% 30.86/21.31  tff(c_873, plain, (k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_846, c_541])).
% 30.86/21.31  tff(c_24, plain, (![A_13, B_14, C_18]: (m1_subset_1('#skF_2'(A_13, B_14, C_18), A_13) | C_18=B_14 | ~m1_subset_1(C_18, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.86/21.31  tff(c_741, plain, (![C_130, A_131, B_132]: (r2_hidden(C_130, A_131) | ~r2_hidden(C_130, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.86/21.31  tff(c_63789, plain, (![B_1597, A_1598, A_1599]: (r2_hidden(B_1597, A_1598) | ~m1_subset_1(A_1599, k1_zfmisc_1(A_1598)) | ~m1_subset_1(B_1597, A_1599) | v1_xboole_0(A_1599))), inference(resolution, [status(thm)], [c_6, c_741])).
% 30.86/21.31  tff(c_63798, plain, (![B_1597]: (r2_hidden(B_1597, '#skF_7') | ~m1_subset_1(B_1597, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_404, c_63789])).
% 30.86/21.31  tff(c_63822, plain, (![B_1600]: (r2_hidden(B_1600, '#skF_7') | ~m1_subset_1(B_1600, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_401, c_63798])).
% 30.86/21.31  tff(c_38, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.86/21.31  tff(c_325, plain, (![C_90, B_91, A_92]: (~v1_xboole_0(C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_101])).
% 30.86/21.31  tff(c_342, plain, (![B_24, A_92, A_23]: (~v1_xboole_0(B_24) | ~r2_hidden(A_92, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_38, c_325])).
% 30.86/21.31  tff(c_63840, plain, (![B_24, B_1600]: (~v1_xboole_0(B_24) | ~r1_tarski('#skF_7', B_24) | ~m1_subset_1(B_1600, '#skF_7'))), inference(resolution, [status(thm)], [c_63822, c_342])).
% 30.86/21.31  tff(c_63850, plain, (![B_1603]: (~m1_subset_1(B_1603, '#skF_7'))), inference(splitLeft, [status(thm)], [c_63840])).
% 30.86/21.31  tff(c_63901, plain, (![C_1607, B_1608]: (C_1607=B_1608 | ~m1_subset_1(C_1607, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_1608, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_63850])).
% 30.86/21.31  tff(c_63932, plain, (![B_1609]: (B_1609='#skF_7' | ~m1_subset_1(B_1609, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_404, c_63901])).
% 30.86/21.31  tff(c_63959, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_63932])).
% 30.86/21.31  tff(c_63973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_63959])).
% 30.86/21.31  tff(c_63974, plain, (![B_24]: (~v1_xboole_0(B_24) | ~r1_tarski('#skF_7', B_24))), inference(splitRight, [status(thm)], [c_63840])).
% 30.86/21.31  tff(c_64481, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_64449, c_63974])).
% 30.86/21.31  tff(c_64503, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_64481])).
% 30.86/21.31  tff(c_64504, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_64503])).
% 30.86/21.31  tff(c_64334, plain, (![A_1640, B_1641]: (m1_subset_1('#skF_4'(A_1640, B_1641), k1_zfmisc_1(u1_struct_0(A_1640))) | v3_tex_2(B_1641, A_1640) | ~v2_tex_2(B_1641, A_1640) | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0(A_1640))) | ~l1_pre_topc(A_1640))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_64376, plain, (![B_1641]: (m1_subset_1('#skF_4'('#skF_6', B_1641), k1_zfmisc_1('#skF_7')) | v3_tex_2(B_1641, '#skF_6') | ~v2_tex_2(B_1641, '#skF_6') | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_64334])).
% 30.86/21.31  tff(c_64395, plain, (![B_1641]: (m1_subset_1('#skF_4'('#skF_6', B_1641), k1_zfmisc_1('#skF_7')) | v3_tex_2(B_1641, '#skF_6') | ~v2_tex_2(B_1641, '#skF_6') | ~m1_subset_1(B_1641, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_399, c_64376])).
% 30.86/21.31  tff(c_60, plain, (![A_38, B_44]: (m1_subset_1('#skF_4'(A_38, B_44), k1_zfmisc_1(u1_struct_0(A_38))) | v3_tex_2(B_44, A_38) | ~v2_tex_2(B_44, A_38) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_36, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.86/21.31  tff(c_69179, plain, (![A_1873, B_1874]: (r1_tarski('#skF_4'(A_1873, B_1874), u1_struct_0(A_1873)) | v3_tex_2(B_1874, A_1873) | ~v2_tex_2(B_1874, A_1873) | ~m1_subset_1(B_1874, k1_zfmisc_1(u1_struct_0(A_1873))) | ~l1_pre_topc(A_1873))), inference(resolution, [status(thm)], [c_64334, c_36])).
% 30.86/21.31  tff(c_69233, plain, (![B_1874]: (r1_tarski('#skF_4'('#skF_6', B_1874), '#skF_7') | v3_tex_2(B_1874, '#skF_6') | ~v2_tex_2(B_1874, '#skF_6') | ~m1_subset_1(B_1874, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_69179])).
% 30.86/21.31  tff(c_72533, plain, (![B_1976]: (r1_tarski('#skF_4'('#skF_6', B_1976), '#skF_7') | v3_tex_2(B_1976, '#skF_6') | ~v2_tex_2(B_1976, '#skF_6') | ~m1_subset_1(B_1976, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_399, c_69233])).
% 30.86/21.31  tff(c_64767, plain, (![A_1667, B_1668, C_1669]: (r2_hidden('#skF_2'(A_1667, B_1668, C_1669), B_1668) | r2_hidden('#skF_2'(A_1667, B_1668, C_1669), C_1669) | C_1669=B_1668 | ~m1_subset_1(C_1669, k1_zfmisc_1(A_1667)) | ~m1_subset_1(B_1668, k1_zfmisc_1(A_1667)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.86/21.31  tff(c_572, plain, (![A_102]: (m1_subset_1(A_102, '#skF_7') | ~r2_hidden(A_102, '#skF_7'))), inference(resolution, [status(thm)], [c_404, c_550])).
% 30.86/21.31  tff(c_64849, plain, (![A_1667, C_1669]: (m1_subset_1('#skF_2'(A_1667, '#skF_7', C_1669), '#skF_7') | r2_hidden('#skF_2'(A_1667, '#skF_7', C_1669), C_1669) | C_1669='#skF_7' | ~m1_subset_1(C_1669, k1_zfmisc_1(A_1667)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1667)))), inference(resolution, [status(thm)], [c_64767, c_572])).
% 30.86/21.31  tff(c_574, plain, (![A_102, B_24, A_23]: (m1_subset_1(A_102, B_24) | ~r2_hidden(A_102, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_38, c_550])).
% 30.86/21.31  tff(c_63839, plain, (![B_1600, B_24]: (m1_subset_1(B_1600, B_24) | ~r1_tarski('#skF_7', B_24) | ~m1_subset_1(B_1600, '#skF_7'))), inference(resolution, [status(thm)], [c_63822, c_574])).
% 30.86/21.31  tff(c_64477, plain, (![B_1600]: (m1_subset_1(B_1600, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1600, '#skF_7') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_64449, c_63839])).
% 30.86/21.31  tff(c_64499, plain, (![B_1600]: (m1_subset_1(B_1600, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1600, '#skF_7') | v3_tex_2('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_64477])).
% 30.86/21.31  tff(c_64500, plain, (![B_1600]: (m1_subset_1(B_1600, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1600, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_64499])).
% 30.86/21.31  tff(c_40, plain, (![A_25, C_27, B_26]: (m1_subset_1(A_25, C_27) | ~m1_subset_1(B_26, k1_zfmisc_1(C_27)) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 30.86/21.31  tff(c_64678, plain, (![A_1661, A_1662, B_1663]: (m1_subset_1(A_1661, A_1662) | ~r2_hidden(A_1661, k1_tarski(B_1663)) | k1_xboole_0=A_1662 | ~m1_subset_1(B_1663, A_1662))), inference(resolution, [status(thm)], [c_666, c_40])).
% 30.86/21.31  tff(c_67253, plain, (![B_1798, A_1799, B_1800]: (m1_subset_1(B_1798, A_1799) | k1_xboole_0=A_1799 | ~m1_subset_1(B_1800, A_1799) | ~m1_subset_1(B_1798, k1_tarski(B_1800)) | v1_xboole_0(k1_tarski(B_1800)))), inference(resolution, [status(thm)], [c_6, c_64678])).
% 30.86/21.31  tff(c_67299, plain, (![B_1798, B_1600]: (m1_subset_1(B_1798, '#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')=k1_xboole_0 | ~m1_subset_1(B_1798, k1_tarski(B_1600)) | v1_xboole_0(k1_tarski(B_1600)) | ~m1_subset_1(B_1600, '#skF_7'))), inference(resolution, [status(thm)], [c_64500, c_67253])).
% 30.86/21.31  tff(c_67621, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_67299])).
% 30.86/21.31  tff(c_67678, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_67621, c_64504])).
% 30.86/21.31  tff(c_67684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_67678])).
% 30.86/21.31  tff(c_67686, plain, ('#skF_4'('#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_67299])).
% 30.86/21.31  tff(c_691, plain, (![B_120, A_121]: (v1_subset_1(k1_tarski(B_120), A_121) | k1_tarski(B_120)=A_121 | k1_xboole_0=A_121 | ~m1_subset_1(B_120, A_121))), inference(resolution, [status(thm)], [c_666, c_50])).
% 30.86/21.31  tff(c_22, plain, (![B_12, A_11]: (m1_subset_1(k1_tarski(B_12), k1_zfmisc_1(A_11)) | k1_xboole_0=A_11 | ~m1_subset_1(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.86/21.31  tff(c_785, plain, (![B_135, A_136]: (~v1_subset_1(B_135, A_136) | v1_xboole_0(B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(A_136)) | ~v1_zfmisc_1(A_136) | v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_122])).
% 30.86/21.31  tff(c_66579, plain, (![B_1762, A_1763]: (~v1_subset_1(k1_tarski(B_1762), A_1763) | v1_xboole_0(k1_tarski(B_1762)) | ~v1_zfmisc_1(A_1763) | v1_xboole_0(A_1763) | k1_xboole_0=A_1763 | ~m1_subset_1(B_1762, A_1763))), inference(resolution, [status(thm)], [c_22, c_785])).
% 30.86/21.31  tff(c_68722, plain, (![B_1866, A_1867]: (v1_xboole_0(k1_tarski(B_1866)) | ~v1_zfmisc_1(A_1867) | v1_xboole_0(A_1867) | k1_tarski(B_1866)=A_1867 | k1_xboole_0=A_1867 | ~m1_subset_1(B_1866, A_1867))), inference(resolution, [status(thm)], [c_691, c_66579])).
% 30.86/21.31  tff(c_68736, plain, (![B_1600]: (v1_xboole_0(k1_tarski(B_1600)) | ~v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | k1_tarski(B_1600)='#skF_4'('#skF_6', '#skF_7') | '#skF_4'('#skF_6', '#skF_7')=k1_xboole_0 | ~m1_subset_1(B_1600, '#skF_7'))), inference(resolution, [status(thm)], [c_64500, c_68722])).
% 30.86/21.31  tff(c_68773, plain, (![B_1600]: (v1_xboole_0(k1_tarski(B_1600)) | ~v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | k1_tarski(B_1600)='#skF_4'('#skF_6', '#skF_7') | ~m1_subset_1(B_1600, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_67686, c_64504, c_68736])).
% 30.86/21.31  tff(c_68816, plain, (~v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_68773])).
% 30.86/21.31  tff(c_453, plain, (![A_97]: (m1_subset_1('#skF_5'(A_97), k1_zfmisc_1(A_97)) | v1_zfmisc_1(A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_165])).
% 30.86/21.31  tff(c_1081, plain, (![A_156]: (v1_subset_1('#skF_5'(A_156), A_156) | '#skF_5'(A_156)=A_156 | v1_zfmisc_1(A_156) | v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_453, c_50])).
% 30.86/21.31  tff(c_66, plain, (![A_48]: (~v1_subset_1('#skF_5'(A_48), A_48) | v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_165])).
% 30.86/21.31  tff(c_1085, plain, (![A_156]: ('#skF_5'(A_156)=A_156 | v1_zfmisc_1(A_156) | v1_xboole_0(A_156))), inference(resolution, [status(thm)], [c_1081, c_66])).
% 30.86/21.31  tff(c_68819, plain, ('#skF_5'('#skF_4'('#skF_6', '#skF_7'))='#skF_4'('#skF_6', '#skF_7') | v1_xboole_0('#skF_4'('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1085, c_68816])).
% 30.86/21.31  tff(c_68822, plain, ('#skF_5'('#skF_4'('#skF_6', '#skF_7'))='#skF_4'('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64504, c_68819])).
% 30.86/21.31  tff(c_72, plain, (![A_48]: (m1_subset_1('#skF_5'(A_48), k1_zfmisc_1(A_48)) | v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_165])).
% 30.86/21.31  tff(c_571, plain, (![A_102, A_48]: (m1_subset_1(A_102, A_48) | ~r2_hidden(A_102, '#skF_5'(A_48)) | v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_72, c_550])).
% 30.86/21.31  tff(c_68849, plain, (![A_102]: (m1_subset_1(A_102, '#skF_4'('#skF_6', '#skF_7')) | ~r2_hidden(A_102, '#skF_4'('#skF_6', '#skF_7')) | v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_68822, c_571])).
% 30.86/21.31  tff(c_69067, plain, (![A_1871]: (m1_subset_1(A_1871, '#skF_4'('#skF_6', '#skF_7')) | ~r2_hidden(A_1871, '#skF_4'('#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64504, c_68816, c_68849])).
% 30.86/21.31  tff(c_69082, plain, (![A_1667]: (m1_subset_1('#skF_2'(A_1667, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_4'('#skF_6', '#skF_7')) | m1_subset_1('#skF_2'(A_1667, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_7') | '#skF_4'('#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1667)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1667)))), inference(resolution, [status(thm)], [c_64849, c_69067])).
% 30.86/21.31  tff(c_69940, plain, (![A_1891]: (m1_subset_1('#skF_2'(A_1891, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_4'('#skF_6', '#skF_7')) | m1_subset_1('#skF_2'(A_1891, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_7') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1891)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1891)))), inference(negUnitSimplification, [status(thm)], [c_64141, c_69082])).
% 30.86/21.31  tff(c_63817, plain, (![B_1597, B_24, A_23]: (r2_hidden(B_1597, B_24) | ~m1_subset_1(B_1597, A_23) | v1_xboole_0(A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_38, c_63789])).
% 30.86/21.31  tff(c_69946, plain, (![A_1891, B_24]: (r2_hidden('#skF_2'(A_1891, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), B_24) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), B_24) | m1_subset_1('#skF_2'(A_1891, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_7') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1891)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1891)))), inference(resolution, [status(thm)], [c_69940, c_63817])).
% 30.86/21.31  tff(c_70194, plain, (![A_1896, B_1897]: (r2_hidden('#skF_2'(A_1896, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), B_1897) | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), B_1897) | m1_subset_1('#skF_2'(A_1896, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_7') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1896)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1896)))), inference(negUnitSimplification, [status(thm)], [c_64504, c_69946])).
% 30.86/21.31  tff(c_70252, plain, (![A_1896]: (~r1_tarski('#skF_4'('#skF_6', '#skF_7'), '#skF_7') | m1_subset_1('#skF_2'(A_1896, '#skF_7', '#skF_4'('#skF_6', '#skF_7')), '#skF_7') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1896)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1896)))), inference(resolution, [status(thm)], [c_70194, c_572])).
% 30.86/21.31  tff(c_70484, plain, (~r1_tarski('#skF_4'('#skF_6', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_70252])).
% 30.86/21.31  tff(c_72539, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_72533, c_70484])).
% 30.86/21.31  tff(c_72590, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_72539])).
% 30.86/21.31  tff(c_72592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_72590])).
% 30.86/21.31  tff(c_72594, plain, (r1_tarski('#skF_4'('#skF_6', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_70252])).
% 30.86/21.31  tff(c_62, plain, (![C_47, B_44, A_38]: (C_47=B_44 | ~r1_tarski(B_44, C_47) | ~v2_tex_2(C_47, A_38) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_38))) | ~v3_tex_2(B_44, A_38) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_72615, plain, (![A_38]: ('#skF_4'('#skF_6', '#skF_7')='#skF_7' | ~v2_tex_2('#skF_7', A_38) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_38))) | ~v3_tex_2('#skF_4'('#skF_6', '#skF_7'), A_38) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_72594, c_62])).
% 30.86/21.31  tff(c_73897, plain, (![A_2011]: (~v2_tex_2('#skF_7', A_2011) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_2011))) | ~v3_tex_2('#skF_4'('#skF_6', '#skF_7'), A_2011) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0(A_2011))) | ~l1_pre_topc(A_2011))), inference(negUnitSimplification, [status(thm)], [c_64141, c_72615])).
% 30.86/21.31  tff(c_73907, plain, (~v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_60, c_73897])).
% 30.86/21.31  tff(c_73921, plain, (~v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_404, c_399, c_1187, c_73907])).
% 30.86/21.31  tff(c_73922, plain, (~v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_135, c_73921])).
% 30.86/21.31  tff(c_112, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.86/21.31  tff(c_131, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_112])).
% 30.86/21.31  tff(c_403, plain, (r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_131])).
% 30.86/21.31  tff(c_64201, plain, (![A_1625, B_1626]: (v2_tex_2('#skF_4'(A_1625, B_1626), A_1625) | v3_tex_2(B_1626, A_1625) | ~v2_tex_2(B_1626, A_1625) | ~m1_subset_1(B_1626, k1_zfmisc_1(u1_struct_0(A_1625))) | ~l1_pre_topc(A_1625))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_64230, plain, (![A_1625, A_23]: (v2_tex_2('#skF_4'(A_1625, A_23), A_1625) | v3_tex_2(A_23, A_1625) | ~v2_tex_2(A_23, A_1625) | ~l1_pre_topc(A_1625) | ~r1_tarski(A_23, u1_struct_0(A_1625)))), inference(resolution, [status(thm)], [c_38, c_64201])).
% 30.86/21.31  tff(c_66833, plain, (![A_1779, A_1780]: (r1_tarski(A_1779, '#skF_4'(A_1780, A_1779)) | v3_tex_2(A_1779, A_1780) | ~v2_tex_2(A_1779, A_1780) | ~l1_pre_topc(A_1780) | ~r1_tarski(A_1779, u1_struct_0(A_1780)))), inference(resolution, [status(thm)], [c_38, c_64008])).
% 30.86/21.31  tff(c_66841, plain, (![A_1779]: (r1_tarski(A_1779, '#skF_4'('#skF_6', A_1779)) | v3_tex_2(A_1779, '#skF_6') | ~v2_tex_2(A_1779, '#skF_6') | ~l1_pre_topc('#skF_6') | ~r1_tarski(A_1779, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_66833])).
% 30.86/21.31  tff(c_66850, plain, (![A_1779]: (r1_tarski(A_1779, '#skF_4'('#skF_6', A_1779)) | v3_tex_2(A_1779, '#skF_6') | ~v2_tex_2(A_1779, '#skF_6') | ~r1_tarski(A_1779, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_66841])).
% 30.86/21.31  tff(c_63812, plain, (![B_1597, A_48]: (r2_hidden(B_1597, A_48) | ~m1_subset_1(B_1597, '#skF_5'(A_48)) | v1_xboole_0('#skF_5'(A_48)) | v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_72, c_63789])).
% 30.86/21.31  tff(c_68834, plain, (![B_1597]: (r2_hidden(B_1597, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1597, '#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_4'('#skF_6', '#skF_7'))) | v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_68822, c_63812])).
% 30.86/21.31  tff(c_68872, plain, (![B_1597]: (r2_hidden(B_1597, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1597, '#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_68822, c_68834])).
% 30.86/21.31  tff(c_69151, plain, (![B_1872]: (r2_hidden(B_1872, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1872, '#skF_4'('#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_64504, c_68816, c_64504, c_68872])).
% 30.86/21.31  tff(c_73937, plain, (![B_2012, B_2013]: (m1_subset_1(B_2012, B_2013) | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), B_2013) | ~m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_69151, c_574])).
% 30.86/21.31  tff(c_73947, plain, (![B_2012]: (m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_66850, c_73937])).
% 30.86/21.31  tff(c_73959, plain, (![B_2012]: (m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72594, c_73947])).
% 30.86/21.31  tff(c_73960, plain, (![B_2012]: (m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_2012, '#skF_4'('#skF_6', '#skF_7')) | ~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_73922, c_73959])).
% 30.86/21.31  tff(c_74034, plain, (~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_73960])).
% 30.86/21.31  tff(c_74037, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_64230, c_74034])).
% 30.86/21.31  tff(c_74049, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_399, c_80, c_1187, c_74037])).
% 30.86/21.31  tff(c_74051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_74049])).
% 30.86/21.31  tff(c_74053, plain, (v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_73960])).
% 30.86/21.31  tff(c_56, plain, (![B_44, A_38]: (r1_tarski(B_44, '#skF_4'(A_38, B_44)) | v3_tex_2(B_44, A_38) | ~v2_tex_2(B_44, A_38) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_64381, plain, (![A_1640, B_1641]: (r1_tarski('#skF_4'(A_1640, B_1641), '#skF_4'(A_1640, '#skF_4'(A_1640, B_1641))) | v3_tex_2('#skF_4'(A_1640, B_1641), A_1640) | ~v2_tex_2('#skF_4'(A_1640, B_1641), A_1640) | v3_tex_2(B_1641, A_1640) | ~v2_tex_2(B_1641, A_1640) | ~m1_subset_1(B_1641, k1_zfmisc_1(u1_struct_0(A_1640))) | ~l1_pre_topc(A_1640))), inference(resolution, [status(thm)], [c_64334, c_56])).
% 30.86/21.31  tff(c_82287, plain, (![A_2203, B_2204]: (r1_tarski('#skF_4'(A_2203, B_2204), '#skF_4'(A_2203, '#skF_4'(A_2203, B_2204))) | v3_tex_2('#skF_4'(A_2203, B_2204), A_2203) | ~v2_tex_2('#skF_4'(A_2203, B_2204), A_2203) | v3_tex_2(B_2204, A_2203) | ~v2_tex_2(B_2204, A_2203) | ~m1_subset_1(B_2204, k1_zfmisc_1(u1_struct_0(A_2203))) | ~l1_pre_topc(A_2203))), inference(resolution, [status(thm)], [c_64334, c_56])).
% 30.86/21.31  tff(c_64514, plain, (![B_1647]: (m1_subset_1(B_1647, '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1(B_1647, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_64499])).
% 30.86/21.31  tff(c_64516, plain, (![B_1647, B_24]: (r2_hidden(B_1647, B_24) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), B_24) | ~m1_subset_1(B_1647, '#skF_7'))), inference(resolution, [status(thm)], [c_64514, c_63817])).
% 30.86/21.31  tff(c_64522, plain, (![B_1647, B_24]: (r2_hidden(B_1647, B_24) | ~r1_tarski('#skF_4'('#skF_6', '#skF_7'), B_24) | ~m1_subset_1(B_1647, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64504, c_64516])).
% 30.86/21.31  tff(c_82327, plain, (![B_1647]: (r2_hidden(B_1647, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_1647, '#skF_7') | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_82287, c_64522])).
% 30.86/21.31  tff(c_82373, plain, (![B_1647]: (r2_hidden(B_1647, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_1647, '#skF_7') | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_404, c_399, c_1187, c_74053, c_82327])).
% 30.86/21.31  tff(c_82381, plain, (![B_2205]: (r2_hidden(B_2205, '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1(B_2205, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_73922, c_82373])).
% 30.86/21.31  tff(c_82416, plain, (![B_24, B_2205]: (~v1_xboole_0(B_24) | ~r1_tarski('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), B_24) | ~m1_subset_1(B_2205, '#skF_7'))), inference(resolution, [status(thm)], [c_82381, c_342])).
% 30.86/21.31  tff(c_82453, plain, (![B_2205]: (~m1_subset_1(B_2205, '#skF_7'))), inference(splitLeft, [status(thm)], [c_82416])).
% 30.86/21.31  tff(c_346, plain, (![A_10, A_92]: (~v1_xboole_0(A_10) | ~r2_hidden(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_325])).
% 30.86/21.31  tff(c_349, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_346])).
% 30.86/21.31  tff(c_64837, plain, (![A_1667, B_1668]: (r2_hidden('#skF_2'(A_1667, B_1668, k1_xboole_0), B_1668) | k1_xboole_0=B_1668 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1667)) | ~m1_subset_1(B_1668, k1_zfmisc_1(A_1667)))), inference(resolution, [status(thm)], [c_64767, c_349])).
% 30.86/21.31  tff(c_65092, plain, (![A_1688, B_1689]: (r2_hidden('#skF_2'(A_1688, B_1689, k1_xboole_0), B_1689) | k1_xboole_0=B_1689 | ~m1_subset_1(B_1689, k1_zfmisc_1(A_1688)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_64837])).
% 30.86/21.31  tff(c_65123, plain, (![A_1688]: (m1_subset_1('#skF_2'(A_1688, '#skF_7', k1_xboole_0), '#skF_7') | k1_xboole_0='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1688)))), inference(resolution, [status(thm)], [c_65092, c_572])).
% 30.86/21.31  tff(c_65144, plain, (![A_1688]: (m1_subset_1('#skF_2'(A_1688, '#skF_7', k1_xboole_0), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1688)))), inference(negUnitSimplification, [status(thm)], [c_873, c_65123])).
% 30.86/21.31  tff(c_82466, plain, (![A_1688]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_1688)))), inference(negUnitSimplification, [status(thm)], [c_82453, c_65144])).
% 30.86/21.31  tff(c_82672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82466, c_404])).
% 30.86/21.31  tff(c_82674, plain, (![B_2209]: (~v1_xboole_0(B_2209) | ~r1_tarski('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), B_2209))), inference(splitRight, [status(thm)], [c_82416])).
% 30.86/21.31  tff(c_82678, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')))) | v3_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64381, c_82674])).
% 30.86/21.31  tff(c_82697, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')))) | v3_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | v3_tex_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_399, c_74053, c_82678])).
% 30.86/21.31  tff(c_82698, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')))) | v3_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | ~v2_tex_2('#skF_4'('#skF_6', '#skF_4'('#skF_6', '#skF_7')), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_73922, c_82697])).
% 30.86/21.31  tff(c_99973, plain, (~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_82698])).
% 30.86/21.31  tff(c_99982, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_64395, c_99973])).
% 30.86/21.31  tff(c_99995, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_99982])).
% 30.86/21.31  tff(c_99997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_99995])).
% 30.86/21.31  tff(c_99999, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1('#skF_7'))), inference(splitRight, [status(thm)], [c_82698])).
% 30.86/21.31  tff(c_65150, plain, (![A_1690]: (m1_subset_1('#skF_2'(A_1690, '#skF_7', k1_xboole_0), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1690)))), inference(negUnitSimplification, [status(thm)], [c_873, c_65123])).
% 30.86/21.31  tff(c_65152, plain, (![A_1690, B_24]: (r2_hidden('#skF_2'(A_1690, '#skF_7', k1_xboole_0), B_24) | v1_xboole_0('#skF_7') | ~r1_tarski('#skF_7', B_24) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1690)))), inference(resolution, [status(thm)], [c_65150, c_63817])).
% 30.86/21.31  tff(c_65734, plain, (![A_1726, B_1727]: (r2_hidden('#skF_2'(A_1726, '#skF_7', k1_xboole_0), B_1727) | ~r1_tarski('#skF_7', B_1727) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1726)))), inference(negUnitSimplification, [status(thm)], [c_401, c_65152])).
% 30.86/21.31  tff(c_4, plain, (![B_2, A_1]: (m1_subset_1(B_2, A_1) | ~r2_hidden(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 30.86/21.31  tff(c_79023, plain, (![A_2130, B_2131]: (m1_subset_1('#skF_2'(A_2130, '#skF_7', k1_xboole_0), B_2131) | v1_xboole_0(B_2131) | ~r1_tarski('#skF_7', B_2131) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2130)))), inference(resolution, [status(thm)], [c_65734, c_4])).
% 30.86/21.31  tff(c_14, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.86/21.31  tff(c_74091, plain, (![B_2023, A_2024]: (r2_hidden(B_2023, A_2024) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2024)) | ~m1_subset_1(B_2023, '#skF_4'('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_69151, c_14])).
% 30.86/21.31  tff(c_74102, plain, (![B_2023]: (r2_hidden(B_2023, '#skF_7') | ~m1_subset_1(B_2023, '#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_64395, c_74091])).
% 30.86/21.31  tff(c_74119, plain, (![B_2023]: (r2_hidden(B_2023, '#skF_7') | ~m1_subset_1(B_2023, '#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_74102])).
% 30.86/21.31  tff(c_74120, plain, (![B_2023]: (r2_hidden(B_2023, '#skF_7') | ~m1_subset_1(B_2023, '#skF_4'('#skF_6', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_135, c_74119])).
% 30.86/21.31  tff(c_79045, plain, (![A_2130]: (r2_hidden('#skF_2'(A_2130, '#skF_7', k1_xboole_0), '#skF_7') | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2130)))), inference(resolution, [status(thm)], [c_79023, c_74120])).
% 30.86/21.31  tff(c_79246, plain, (![A_2130]: (r2_hidden('#skF_2'(A_2130, '#skF_7', k1_xboole_0), '#skF_7') | ~r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2130)))), inference(negUnitSimplification, [status(thm)], [c_64504, c_79045])).
% 30.86/21.31  tff(c_79370, plain, (~r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_79246])).
% 30.86/21.31  tff(c_79373, plain, (v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_66850, c_79370])).
% 30.86/21.31  tff(c_79379, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_1187, c_79373])).
% 30.86/21.31  tff(c_79381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_79379])).
% 30.86/21.31  tff(c_79383, plain, (r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_79246])).
% 30.86/21.31  tff(c_64858, plain, (![A_1667, B_1668, C_1669, A_4]: (r2_hidden('#skF_2'(A_1667, B_1668, C_1669), A_4) | ~m1_subset_1(C_1669, k1_zfmisc_1(A_4)) | r2_hidden('#skF_2'(A_1667, B_1668, C_1669), B_1668) | C_1669=B_1668 | ~m1_subset_1(C_1669, k1_zfmisc_1(A_1667)) | ~m1_subset_1(B_1668, k1_zfmisc_1(A_1667)))), inference(resolution, [status(thm)], [c_64767, c_14])).
% 30.86/21.31  tff(c_77997, plain, (![C_1669, B_1668, A_1667]: (~m1_subset_1(C_1669, k1_zfmisc_1(B_1668)) | C_1669=B_1668 | ~m1_subset_1(C_1669, k1_zfmisc_1(A_1667)) | ~m1_subset_1(B_1668, k1_zfmisc_1(A_1667)) | r2_hidden('#skF_2'(A_1667, B_1668, C_1669), B_1668))), inference(factorization, [status(thm), theory('equality')], [c_64858])).
% 30.86/21.31  tff(c_76083, plain, (![A_2064, B_2065, C_2066]: (m1_subset_1('#skF_2'(A_2064, B_2065, C_2066), B_2065) | v1_xboole_0(B_2065) | r2_hidden('#skF_2'(A_2064, B_2065, C_2066), C_2066) | C_2066=B_2065 | ~m1_subset_1(C_2066, k1_zfmisc_1(A_2064)) | ~m1_subset_1(B_2065, k1_zfmisc_1(A_2064)))), inference(resolution, [status(thm)], [c_64767, c_4])).
% 30.86/21.31  tff(c_76098, plain, (![A_2064, C_2066]: (r2_hidden('#skF_2'(A_2064, '#skF_4'('#skF_6', '#skF_7'), C_2066), '#skF_7') | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | r2_hidden('#skF_2'(A_2064, '#skF_4'('#skF_6', '#skF_7'), C_2066), C_2066) | C_2066='#skF_4'('#skF_6', '#skF_7') | ~m1_subset_1(C_2066, k1_zfmisc_1(A_2064)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2064)))), inference(resolution, [status(thm)], [c_76083, c_74120])).
% 30.86/21.31  tff(c_76375, plain, (![A_2064, C_2066]: (r2_hidden('#skF_2'(A_2064, '#skF_4'('#skF_6', '#skF_7'), C_2066), '#skF_7') | r2_hidden('#skF_2'(A_2064, '#skF_4'('#skF_6', '#skF_7'), C_2066), C_2066) | C_2066='#skF_4'('#skF_6', '#skF_7') | ~m1_subset_1(C_2066, k1_zfmisc_1(A_2064)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2064)))), inference(negUnitSimplification, [status(thm)], [c_64504, c_76098])).
% 30.86/21.31  tff(c_100623, plain, (![A_2064]: ('#skF_4'('#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2064)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2064)) | r2_hidden('#skF_2'(A_2064, '#skF_4'('#skF_6', '#skF_7'), '#skF_7'), '#skF_7'))), inference(factorization, [status(thm), theory('equality')], [c_76375])).
% 30.86/21.31  tff(c_101147, plain, (![A_2572]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_2572)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2572)) | r2_hidden('#skF_2'(A_2572, '#skF_4'('#skF_6', '#skF_7'), '#skF_7'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64141, c_100623])).
% 30.86/21.31  tff(c_26, plain, (![A_13, B_14, C_18]: (~r2_hidden('#skF_2'(A_13, B_14, C_18), C_18) | ~r2_hidden('#skF_2'(A_13, B_14, C_18), B_14) | C_18=B_14 | ~m1_subset_1(C_18, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.86/21.31  tff(c_101149, plain, (![A_2572]: (~r2_hidden('#skF_2'(A_2572, '#skF_4'('#skF_6', '#skF_7'), '#skF_7'), '#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2572)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2572)))), inference(resolution, [status(thm)], [c_101147, c_26])).
% 30.86/21.31  tff(c_103026, plain, (![A_2604]: (~r2_hidden('#skF_2'(A_2604, '#skF_4'('#skF_6', '#skF_7'), '#skF_7'), '#skF_4'('#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_2604)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2604)))), inference(negUnitSimplification, [status(thm)], [c_64141, c_101149])).
% 30.86/21.31  tff(c_103034, plain, (![A_1667]: (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'('#skF_6', '#skF_7'))) | '#skF_4'('#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1667)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1667)))), inference(resolution, [status(thm)], [c_77997, c_103026])).
% 30.86/21.31  tff(c_103088, plain, (![A_1667]: (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'('#skF_6', '#skF_7'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1667)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_1667)))), inference(negUnitSimplification, [status(thm)], [c_64141, c_103034])).
% 30.86/21.31  tff(c_103593, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_103088])).
% 30.86/21.31  tff(c_103602, plain, (~r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_103593])).
% 30.86/21.31  tff(c_103611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79383, c_103602])).
% 30.86/21.31  tff(c_104886, plain, (![A_2631]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_2631)) | ~m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(A_2631)))), inference(splitRight, [status(thm)], [c_103088])).
% 30.86/21.31  tff(c_104897, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_99999, c_104886])).
% 30.86/21.31  tff(c_104936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_104897])).
% 30.86/21.31  tff(c_104938, plain, (v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_68773])).
% 30.86/21.31  tff(c_1384, plain, (![A_185, B_186]: ('#skF_4'(A_185, B_186)!=B_186 | v3_tex_2(B_186, A_185) | ~v2_tex_2(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_1399, plain, (![B_186]: ('#skF_4'('#skF_6', B_186)!=B_186 | v3_tex_2(B_186, '#skF_6') | ~v2_tex_2(B_186, '#skF_6') | ~m1_subset_1(B_186, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1384])).
% 30.86/21.31  tff(c_1868, plain, (![B_228]: ('#skF_4'('#skF_6', B_228)!=B_228 | v3_tex_2(B_228, '#skF_6') | ~v2_tex_2(B_228, '#skF_6') | ~m1_subset_1(B_228, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1399])).
% 30.86/21.31  tff(c_1883, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_404, c_1868])).
% 30.86/21.31  tff(c_1905, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1883])).
% 30.86/21.31  tff(c_1906, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_135, c_1905])).
% 30.86/21.31  tff(c_1806, plain, (![B_222, A_223]: (r1_tarski(B_222, '#skF_4'(A_223, B_222)) | v3_tex_2(B_222, A_223) | ~v2_tex_2(B_222, A_223) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_1817, plain, (![B_222]: (r1_tarski(B_222, '#skF_4'('#skF_6', B_222)) | v3_tex_2(B_222, '#skF_6') | ~v2_tex_2(B_222, '#skF_6') | ~m1_subset_1(B_222, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_1806])).
% 30.86/21.31  tff(c_4297, plain, (![B_373]: (r1_tarski(B_373, '#skF_4'('#skF_6', B_373)) | v3_tex_2(B_373, '#skF_6') | ~v2_tex_2(B_373, '#skF_6') | ~m1_subset_1(B_373, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1817])).
% 30.86/21.31  tff(c_1327, plain, (![B_181, A_182, A_183]: (r2_hidden(B_181, A_182) | ~m1_subset_1(A_183, k1_zfmisc_1(A_182)) | ~m1_subset_1(B_181, A_183) | v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_6, c_741])).
% 30.86/21.31  tff(c_1336, plain, (![B_181]: (r2_hidden(B_181, '#skF_7') | ~m1_subset_1(B_181, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_404, c_1327])).
% 30.86/21.31  tff(c_1360, plain, (![B_184]: (r2_hidden(B_184, '#skF_7') | ~m1_subset_1(B_184, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_401, c_1336])).
% 30.86/21.31  tff(c_1378, plain, (![B_24, B_184]: (~v1_xboole_0(B_24) | ~r1_tarski('#skF_7', B_24) | ~m1_subset_1(B_184, '#skF_7'))), inference(resolution, [status(thm)], [c_1360, c_342])).
% 30.86/21.31  tff(c_1428, plain, (![B_189]: (~m1_subset_1(B_189, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1378])).
% 30.86/21.31  tff(c_1446, plain, (![C_191, B_192]: (C_191=B_192 | ~m1_subset_1(C_191, k1_zfmisc_1('#skF_7')) | ~m1_subset_1(B_192, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_24, c_1428])).
% 30.86/21.31  tff(c_1510, plain, (![B_195]: (k1_xboole_0=B_195 | ~m1_subset_1(B_195, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_20, c_1446])).
% 30.86/21.31  tff(c_1525, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_404, c_1510])).
% 30.86/21.31  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_873, c_1525])).
% 30.86/21.31  tff(c_1548, plain, (![B_24]: (~v1_xboole_0(B_24) | ~r1_tarski('#skF_7', B_24))), inference(splitRight, [status(thm)], [c_1378])).
% 30.86/21.31  tff(c_4371, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_4297, c_1548])).
% 30.86/21.31  tff(c_4408, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_1187, c_4371])).
% 30.86/21.31  tff(c_4409, plain, (~v1_xboole_0('#skF_4'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_4408])).
% 30.86/21.31  tff(c_1164, plain, (v2_tex_2('#skF_5'('#skF_7'), '#skF_6') | v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_72, c_1152])).
% 30.86/21.31  tff(c_1186, plain, (v2_tex_2('#skF_5'('#skF_7'), '#skF_6') | v1_zfmisc_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_401, c_1164])).
% 30.86/21.31  tff(c_1192, plain, (v1_zfmisc_1('#skF_7')), inference(splitLeft, [status(thm)], [c_1186])).
% 30.86/21.31  tff(c_1966, plain, (![A_231, B_232]: (m1_subset_1('#skF_4'(A_231, B_232), k1_zfmisc_1(u1_struct_0(A_231))) | v3_tex_2(B_232, A_231) | ~v2_tex_2(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_61680, plain, (![A_1511, B_1512]: (r1_tarski('#skF_4'(A_1511, B_1512), u1_struct_0(A_1511)) | v3_tex_2(B_1512, A_1511) | ~v2_tex_2(B_1512, A_1511) | ~m1_subset_1(B_1512, k1_zfmisc_1(u1_struct_0(A_1511))) | ~l1_pre_topc(A_1511))), inference(resolution, [status(thm)], [c_1966, c_36])).
% 30.86/21.31  tff(c_61734, plain, (![B_1512]: (r1_tarski('#skF_4'('#skF_6', B_1512), '#skF_7') | v3_tex_2(B_1512, '#skF_6') | ~v2_tex_2(B_1512, '#skF_6') | ~m1_subset_1(B_1512, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_61680])).
% 30.86/21.31  tff(c_62035, plain, (![B_1524]: (r1_tarski('#skF_4'('#skF_6', B_1524), '#skF_7') | v3_tex_2(B_1524, '#skF_6') | ~v2_tex_2(B_1524, '#skF_6') | ~m1_subset_1(B_1524, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_399, c_61734])).
% 30.86/21.31  tff(c_394, plain, (![A_23, B_24]: (v1_subset_1(A_23, B_24) | B_24=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_38, c_370])).
% 30.86/21.31  tff(c_2084, plain, (![A_240, B_241]: (~v1_subset_1(A_240, B_241) | v1_xboole_0(A_240) | ~v1_zfmisc_1(B_241) | v1_xboole_0(B_241) | ~r1_tarski(A_240, B_241))), inference(resolution, [status(thm)], [c_38, c_785])).
% 30.86/21.31  tff(c_2106, plain, (![A_23, B_24]: (v1_xboole_0(A_23) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | B_24=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_394, c_2084])).
% 30.86/21.31  tff(c_62059, plain, (![B_1524]: (v1_xboole_0('#skF_4'('#skF_6', B_1524)) | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | '#skF_4'('#skF_6', B_1524)='#skF_7' | v3_tex_2(B_1524, '#skF_6') | ~v2_tex_2(B_1524, '#skF_6') | ~m1_subset_1(B_1524, k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_62035, c_2106])).
% 30.86/21.31  tff(c_62087, plain, (![B_1524]: (v1_xboole_0('#skF_4'('#skF_6', B_1524)) | v1_xboole_0('#skF_7') | '#skF_4'('#skF_6', B_1524)='#skF_7' | v3_tex_2(B_1524, '#skF_6') | ~v2_tex_2(B_1524, '#skF_6') | ~m1_subset_1(B_1524, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_62059])).
% 30.86/21.31  tff(c_63454, plain, (![B_1575]: (v1_xboole_0('#skF_4'('#skF_6', B_1575)) | '#skF_4'('#skF_6', B_1575)='#skF_7' | v3_tex_2(B_1575, '#skF_6') | ~v2_tex_2(B_1575, '#skF_6') | ~m1_subset_1(B_1575, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_401, c_62087])).
% 30.86/21.31  tff(c_63488, plain, (v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_404, c_63454])).
% 30.86/21.31  tff(c_63523, plain, (v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')='#skF_7' | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_63488])).
% 30.86/21.31  tff(c_63525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_1906, c_4409, c_63523])).
% 30.86/21.31  tff(c_63527, plain, (~v1_zfmisc_1('#skF_7')), inference(splitRight, [status(thm)], [c_1186])).
% 30.86/21.31  tff(c_63530, plain, ('#skF_5'('#skF_7')='#skF_7' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1085, c_63527])).
% 30.86/21.31  tff(c_63533, plain, ('#skF_5'('#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_401, c_63530])).
% 30.86/21.31  tff(c_114473, plain, (![A_2845]: (r1_tarski('#skF_5'(u1_struct_0(A_2845)), '#skF_4'(A_2845, '#skF_5'(u1_struct_0(A_2845)))) | v3_tex_2('#skF_5'(u1_struct_0(A_2845)), A_2845) | ~v2_tex_2('#skF_5'(u1_struct_0(A_2845)), A_2845) | ~l1_pre_topc(A_2845) | v1_zfmisc_1(u1_struct_0(A_2845)) | v1_xboole_0(u1_struct_0(A_2845)))), inference(resolution, [status(thm)], [c_72, c_64008])).
% 30.86/21.31  tff(c_114519, plain, (r1_tarski('#skF_5'('#skF_7'), '#skF_4'('#skF_6', '#skF_5'(u1_struct_0('#skF_6')))) | v3_tex_2('#skF_5'(u1_struct_0('#skF_6')), '#skF_6') | ~v2_tex_2('#skF_5'(u1_struct_0('#skF_6')), '#skF_6') | ~l1_pre_topc('#skF_6') | v1_zfmisc_1(u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_114473])).
% 30.86/21.31  tff(c_114543, plain, (r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_399, c_80, c_1187, c_63533, c_399, c_63533, c_399, c_63533, c_399, c_63533, c_114519])).
% 30.86/21.31  tff(c_114544, plain, (r1_tarski('#skF_7', '#skF_4'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_401, c_63527, c_135, c_114543])).
% 30.86/21.31  tff(c_63700, plain, (![A_1591, B_1592]: (~v1_subset_1(A_1591, B_1592) | v1_xboole_0(A_1591) | ~v1_zfmisc_1(B_1592) | v1_xboole_0(B_1592) | ~r1_tarski(A_1591, B_1592))), inference(resolution, [status(thm)], [c_38, c_785])).
% 30.86/21.31  tff(c_63722, plain, (![A_23, B_24]: (v1_xboole_0(A_23) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | B_24=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_394, c_63700])).
% 30.86/21.31  tff(c_114616, plain, (v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_4'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_114544, c_63722])).
% 30.86/21.31  tff(c_114667, plain, (v1_xboole_0('#skF_7') | v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | '#skF_4'('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_104938, c_114616])).
% 30.86/21.31  tff(c_114669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64141, c_64504, c_401, c_114667])).
% 30.86/21.31  tff(c_114719, plain, (![B_2848]: (v1_xboole_0(k1_tarski(B_2848)) | ~v1_xboole_0(B_2848))), inference(splitRight, [status(thm)], [c_777])).
% 30.86/21.31  tff(c_2, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 30.86/21.31  tff(c_12, plain, (![A_3]: (~v1_xboole_0(k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.86/21.31  tff(c_99, plain, (~v1_xboole_0(k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_12])).
% 30.86/21.31  tff(c_114722, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_114719, c_99])).
% 30.86/21.31  tff(c_114726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_114722])).
% 30.86/21.31  tff(c_114728, plain, (~v1_xboole_0('#skF_3'('#skF_6'))), inference(splitRight, [status(thm)], [c_612])).
% 30.86/21.31  tff(c_114731, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_44, c_114728])).
% 30.86/21.31  tff(c_114735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_114731])).
% 30.86/21.31  tff(c_114736, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_269])).
% 30.86/21.31  tff(c_115169, plain, (![B_2892, A_2893]: (m1_subset_1(k1_tarski(B_2892), k1_zfmisc_1(A_2893)) | k1_xboole_0=A_2893 | ~m1_subset_1(B_2892, A_2893))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.86/21.31  tff(c_115212, plain, (![B_2896, A_2897]: (v1_xboole_0(k1_tarski(B_2896)) | ~v1_xboole_0(A_2897) | k1_xboole_0=A_2897 | ~m1_subset_1(B_2896, A_2897))), inference(resolution, [status(thm)], [c_115169, c_34])).
% 30.86/21.31  tff(c_115241, plain, (![B_2, A_1]: (v1_xboole_0(k1_tarski(B_2)) | k1_xboole_0=A_1 | ~v1_xboole_0(B_2) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_8, c_115212])).
% 30.86/21.31  tff(c_115249, plain, (![A_2898]: (k1_xboole_0=A_2898 | ~v1_xboole_0(A_2898))), inference(splitLeft, [status(thm)], [c_115241])).
% 30.86/21.31  tff(c_115262, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_114736, c_115249])).
% 30.86/21.31  tff(c_103, plain, (![A_59]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.86/21.31  tff(c_105, plain, (m1_subset_1(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103])).
% 30.86/21.31  tff(c_115325, plain, (m1_subset_1('#skF_7', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_115262, c_115262, c_105])).
% 30.86/21.31  tff(c_115328, plain, (k1_zfmisc_1('#skF_7')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_115262, c_115262, c_2])).
% 30.86/21.31  tff(c_114795, plain, (![B_2854, A_2855]: (v1_subset_1(B_2854, A_2855) | B_2854=A_2855 | ~m1_subset_1(B_2854, k1_zfmisc_1(A_2855)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 30.86/21.31  tff(c_114811, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_114795])).
% 30.86/21.31  tff(c_114824, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_197, c_114811])).
% 30.86/21.31  tff(c_115468, plain, (![B_2906, A_2907]: (v2_tex_2(B_2906, A_2907) | ~m1_subset_1(B_2906, k1_zfmisc_1(u1_struct_0(A_2907))) | ~l1_pre_topc(A_2907) | ~v1_tdlat_3(A_2907) | ~v2_pre_topc(A_2907) | v2_struct_0(A_2907))), inference(cnfTransformation, [status(thm)], [f_179])).
% 30.86/21.31  tff(c_115479, plain, (![B_2906]: (v2_tex_2(B_2906, '#skF_6') | ~m1_subset_1(B_2906, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_114824, c_115468])).
% 30.86/21.31  tff(c_115494, plain, (![B_2906]: (v2_tex_2(B_2906, '#skF_6') | ~m1_subset_1(B_2906, k1_tarski('#skF_7')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_115328, c_115479])).
% 30.86/21.31  tff(c_115511, plain, (![B_2909]: (v2_tex_2(B_2909, '#skF_6') | ~m1_subset_1(B_2909, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_86, c_115494])).
% 30.86/21.31  tff(c_115519, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_115325, c_115511])).
% 30.86/21.31  tff(c_115737, plain, (![A_2931, B_2932]: ('#skF_4'(A_2931, B_2932)!=B_2932 | v3_tex_2(B_2932, A_2931) | ~v2_tex_2(B_2932, A_2931) | ~m1_subset_1(B_2932, k1_zfmisc_1(u1_struct_0(A_2931))) | ~l1_pre_topc(A_2931))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_115752, plain, (![B_2932]: ('#skF_4'('#skF_6', B_2932)!=B_2932 | v3_tex_2(B_2932, '#skF_6') | ~v2_tex_2(B_2932, '#skF_6') | ~m1_subset_1(B_2932, k1_zfmisc_1('#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_114824, c_115737])).
% 30.86/21.31  tff(c_115921, plain, (![B_2948]: ('#skF_4'('#skF_6', B_2948)!=B_2948 | v3_tex_2(B_2948, '#skF_6') | ~v2_tex_2(B_2948, '#skF_6') | ~m1_subset_1(B_2948, k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_115328, c_115752])).
% 30.86/21.31  tff(c_115931, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_115325, c_115921])).
% 30.86/21.31  tff(c_115940, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_115519, c_115931])).
% 30.86/21.31  tff(c_115941, plain, ('#skF_4'('#skF_6', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_135, c_115940])).
% 30.86/21.31  tff(c_116117, plain, (![A_2971, B_2972]: (m1_subset_1('#skF_4'(A_2971, B_2972), k1_zfmisc_1(u1_struct_0(A_2971))) | v3_tex_2(B_2972, A_2971) | ~v2_tex_2(B_2972, A_2971) | ~m1_subset_1(B_2972, k1_zfmisc_1(u1_struct_0(A_2971))) | ~l1_pre_topc(A_2971))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_116159, plain, (![B_2972]: (m1_subset_1('#skF_4'('#skF_6', B_2972), k1_zfmisc_1('#skF_7')) | v3_tex_2(B_2972, '#skF_6') | ~v2_tex_2(B_2972, '#skF_6') | ~m1_subset_1(B_2972, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_114824, c_116117])).
% 30.86/21.31  tff(c_116386, plain, (![B_2995]: (m1_subset_1('#skF_4'('#skF_6', B_2995), k1_tarski('#skF_7')) | v3_tex_2(B_2995, '#skF_6') | ~v2_tex_2(B_2995, '#skF_6') | ~m1_subset_1(B_2995, k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_115328, c_114824, c_115328, c_116159])).
% 30.86/21.31  tff(c_263, plain, (![B_84]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_tarski(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_241])).
% 30.86/21.31  tff(c_114761, plain, (![B_84]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_tarski(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_263])).
% 30.86/21.31  tff(c_115318, plain, (![B_84]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_115262, c_114761])).
% 30.86/21.31  tff(c_117329, plain, (![B_3065]: (v1_xboole_0('#skF_4'('#skF_6', B_3065)) | v3_tex_2(B_3065, '#skF_6') | ~v2_tex_2(B_3065, '#skF_6') | ~m1_subset_1(B_3065, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_116386, c_115318])).
% 30.86/21.31  tff(c_117342, plain, (v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_115325, c_117329])).
% 30.86/21.31  tff(c_117352, plain, (v1_xboole_0('#skF_4'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_115519, c_117342])).
% 30.86/21.31  tff(c_117353, plain, (v1_xboole_0('#skF_4'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_135, c_117352])).
% 30.86/21.31  tff(c_115248, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(splitLeft, [status(thm)], [c_115241])).
% 30.86/21.31  tff(c_115308, plain, (![A_1]: (A_1='#skF_7' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_115262, c_115248])).
% 30.86/21.31  tff(c_117357, plain, ('#skF_4'('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_117353, c_115308])).
% 30.86/21.31  tff(c_117361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115941, c_117357])).
% 30.86/21.31  tff(c_117404, plain, (![B_3068]: (v1_xboole_0(k1_tarski(B_3068)) | ~v1_xboole_0(B_3068))), inference(splitRight, [status(thm)], [c_115241])).
% 30.86/21.31  tff(c_117407, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_117404, c_99])).
% 30.86/21.31  tff(c_117411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_117407])).
% 30.86/21.31  tff(c_117413, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_88])).
% 30.86/21.31  tff(c_118246, plain, (![B_3153, A_3154]: (~v3_tex_2(B_3153, A_3154) | ~m1_subset_1(B_3153, k1_zfmisc_1(u1_struct_0(A_3154))) | ~v1_xboole_0(B_3153) | ~l1_pre_topc(A_3154) | ~v2_pre_topc(A_3154) | v2_struct_0(A_3154))), inference(cnfTransformation, [status(thm)], [f_194])).
% 30.86/21.31  tff(c_118272, plain, (~v3_tex_2('#skF_7', '#skF_6') | ~v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_78, c_118246])).
% 30.86/21.31  tff(c_118285, plain, (~v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_117413, c_118272])).
% 30.86/21.31  tff(c_118286, plain, (~v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_86, c_118285])).
% 30.86/21.31  tff(c_117549, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_117521])).
% 30.86/21.31  tff(c_117563, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_117549])).
% 30.86/21.31  tff(c_117412, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_88])).
% 30.86/21.31  tff(c_117955, plain, (![B_3136, A_3137]: (~v1_subset_1(B_3136, A_3137) | v1_xboole_0(B_3136) | ~m1_subset_1(B_3136, k1_zfmisc_1(A_3137)) | ~v1_zfmisc_1(A_3137) | v1_xboole_0(A_3137))), inference(cnfTransformation, [status(thm)], [f_122])).
% 30.86/21.31  tff(c_117977, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v1_xboole_0('#skF_7') | ~v1_zfmisc_1(u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_117955])).
% 30.86/21.31  tff(c_117993, plain, (v1_xboole_0('#skF_7') | ~v1_zfmisc_1(u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_117412, c_117977])).
% 30.86/21.31  tff(c_117994, plain, (v1_xboole_0('#skF_7') | ~v1_zfmisc_1(u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_117563, c_117993])).
% 30.86/21.31  tff(c_118017, plain, (~v1_zfmisc_1(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_117994])).
% 30.86/21.31  tff(c_117688, plain, (![A_3103]: (m1_subset_1('#skF_5'(A_3103), k1_zfmisc_1(A_3103)) | v1_zfmisc_1(A_3103) | v1_xboole_0(A_3103))), inference(cnfTransformation, [status(thm)], [f_165])).
% 30.86/21.31  tff(c_118201, plain, (![A_3151]: (v1_subset_1('#skF_5'(A_3151), A_3151) | '#skF_5'(A_3151)=A_3151 | v1_zfmisc_1(A_3151) | v1_xboole_0(A_3151))), inference(resolution, [status(thm)], [c_117688, c_50])).
% 30.86/21.31  tff(c_118206, plain, (![A_3152]: ('#skF_5'(A_3152)=A_3152 | v1_zfmisc_1(A_3152) | v1_xboole_0(A_3152))), inference(resolution, [status(thm)], [c_118201, c_66])).
% 30.86/21.31  tff(c_118209, plain, ('#skF_5'(u1_struct_0('#skF_6'))=u1_struct_0('#skF_6') | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_118206, c_118017])).
% 30.86/21.31  tff(c_118215, plain, ('#skF_5'(u1_struct_0('#skF_6'))=u1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_117563, c_118209])).
% 30.86/21.31  tff(c_118223, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v1_zfmisc_1(u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_118215, c_72])).
% 30.86/21.31  tff(c_118236, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_117563, c_118017, c_118223])).
% 30.86/21.31  tff(c_74, plain, (![B_52, A_50]: (v2_tex_2(B_52, A_50) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v1_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_179])).
% 30.86/21.31  tff(c_118302, plain, (v2_tex_2(u1_struct_0('#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v1_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_118236, c_74])).
% 30.86/21.31  tff(c_118334, plain, (v2_tex_2(u1_struct_0('#skF_6'), '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_118302])).
% 30.86/21.31  tff(c_118335, plain, (v2_tex_2(u1_struct_0('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_86, c_118334])).
% 30.86/21.31  tff(c_119650, plain, (![C_3252, B_3253, A_3254]: (C_3252=B_3253 | ~r1_tarski(B_3253, C_3252) | ~v2_tex_2(C_3252, A_3254) | ~m1_subset_1(C_3252, k1_zfmisc_1(u1_struct_0(A_3254))) | ~v3_tex_2(B_3253, A_3254) | ~m1_subset_1(B_3253, k1_zfmisc_1(u1_struct_0(A_3254))) | ~l1_pre_topc(A_3254))), inference(cnfTransformation, [status(thm)], [f_147])).
% 30.86/21.31  tff(c_119668, plain, (![A_3254]: (u1_struct_0('#skF_6')='#skF_7' | ~v2_tex_2(u1_struct_0('#skF_6'), A_3254) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_3254))) | ~v3_tex_2('#skF_7', A_3254) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_3254))) | ~l1_pre_topc(A_3254))), inference(resolution, [status(thm)], [c_131, c_119650])).
% 30.86/21.31  tff(c_119992, plain, (![A_3288]: (~v2_tex_2(u1_struct_0('#skF_6'), A_3288) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_3288))) | ~v3_tex_2('#skF_7', A_3288) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_3288))) | ~l1_pre_topc(A_3288))), inference(splitLeft, [status(thm)], [c_119668])).
% 30.86/21.31  tff(c_119995, plain, (~v2_tex_2(u1_struct_0('#skF_6'), '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_118236, c_119992])).
% 30.86/21.31  tff(c_120005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_117413, c_118335, c_119995])).
% 30.86/21.31  tff(c_120006, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_119668])).
% 30.86/21.31  tff(c_120025, plain, (~v1_zfmisc_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120006, c_118017])).
% 30.86/21.31  tff(c_120028, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120006, c_117412])).
% 30.86/21.31  tff(c_118205, plain, (![A_3151]: ('#skF_5'(A_3151)=A_3151 | v1_zfmisc_1(A_3151) | v1_xboole_0(A_3151))), inference(resolution, [status(thm)], [c_118201, c_66])).
% 30.86/21.31  tff(c_120094, plain, ('#skF_5'('#skF_7')='#skF_7' | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_118205, c_120025])).
% 30.86/21.31  tff(c_120097, plain, ('#skF_5'('#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_118286, c_120094])).
% 30.86/21.31  tff(c_120138, plain, (~v1_subset_1('#skF_7', '#skF_7') | v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_120097, c_66])).
% 30.86/21.31  tff(c_120152, plain, (v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120028, c_120138])).
% 30.86/21.31  tff(c_120154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118286, c_120025, c_120152])).
% 30.86/21.31  tff(c_120155, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_117994])).
% 30.86/21.31  tff(c_120250, plain, (![B_3294, A_3295]: (~v3_tex_2(B_3294, A_3295) | ~m1_subset_1(B_3294, k1_zfmisc_1(u1_struct_0(A_3295))) | ~v1_xboole_0(B_3294) | ~l1_pre_topc(A_3295) | ~v2_pre_topc(A_3295) | v2_struct_0(A_3295))), inference(cnfTransformation, [status(thm)], [f_194])).
% 30.86/21.31  tff(c_120268, plain, (~v3_tex_2('#skF_7', '#skF_6') | ~v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_78, c_120250])).
% 30.86/21.31  tff(c_120275, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_120155, c_117413, c_120268])).
% 30.86/21.31  tff(c_120277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_120275])).
% 30.86/21.31  tff(c_120278, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_117549])).
% 30.86/21.31  tff(c_120508, plain, (![B_3321, A_3322]: (m1_subset_1(k1_tarski(B_3321), k1_zfmisc_1(A_3322)) | k1_xboole_0=A_3322 | ~m1_subset_1(B_3321, A_3322))), inference(cnfTransformation, [status(thm)], [f_63])).
% 30.86/21.31  tff(c_120623, plain, (![B_3341, A_3342]: (v1_xboole_0(k1_tarski(B_3341)) | ~v1_xboole_0(A_3342) | k1_xboole_0=A_3342 | ~m1_subset_1(B_3341, A_3342))), inference(resolution, [status(thm)], [c_120508, c_34])).
% 30.86/21.31  tff(c_120651, plain, (![B_2, A_1]: (v1_xboole_0(k1_tarski(B_2)) | k1_xboole_0=A_1 | ~v1_xboole_0(B_2) | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_8, c_120623])).
% 30.86/21.31  tff(c_120702, plain, (![A_3345]: (k1_xboole_0=A_3345 | ~v1_xboole_0(A_3345))), inference(splitLeft, [status(thm)], [c_120651])).
% 30.86/21.31  tff(c_120719, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_120278, c_120702])).
% 30.86/21.31  tff(c_117457, plain, (![B_3075]: (~v1_subset_1(B_3075, B_3075) | ~m1_subset_1(B_3075, k1_zfmisc_1(B_3075)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 30.86/21.31  tff(c_117475, plain, (~v1_subset_1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_117457])).
% 30.86/21.31  tff(c_120738, plain, (~v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120719, c_120719, c_117475])).
% 30.86/21.31  tff(c_120279, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_117549])).
% 30.86/21.31  tff(c_120718, plain, (u1_struct_0('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_120279, c_120702])).
% 30.86/21.31  tff(c_120750, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_120719, c_120718])).
% 30.86/21.31  tff(c_120752, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120750, c_117412])).
% 30.86/21.31  tff(c_120798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120738, c_120752])).
% 30.86/21.31  tff(c_120841, plain, (![B_3350]: (v1_xboole_0(k1_tarski(B_3350)) | ~v1_xboole_0(B_3350))), inference(splitRight, [status(thm)], [c_120651])).
% 30.86/21.31  tff(c_120844, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_120841, c_99])).
% 30.86/21.31  tff(c_120848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117562, c_120844])).
% 30.86/21.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.86/21.31  
% 30.86/21.31  Inference rules
% 30.86/21.31  ----------------------
% 30.86/21.31  #Ref     : 0
% 30.86/21.31  #Sup     : 24438
% 30.86/21.31  #Fact    : 41
% 30.86/21.31  #Define  : 0
% 30.86/21.31  #Split   : 176
% 30.86/21.31  #Chain   : 0
% 30.86/21.31  #Close   : 0
% 30.86/21.31  
% 30.86/21.31  Ordering : KBO
% 30.86/21.31  
% 30.86/21.31  Simplification rules
% 30.86/21.31  ----------------------
% 30.86/21.31  #Subsume      : 9434
% 30.86/21.31  #Demod        : 14246
% 30.86/21.31  #Tautology    : 3383
% 30.86/21.31  #SimpNegUnit  : 7575
% 30.86/21.31  #BackRed      : 578
% 30.86/21.31  
% 30.86/21.31  #Partial instantiations: 0
% 30.86/21.31  #Strategies tried      : 1
% 30.86/21.31  
% 30.86/21.31  Timing (in seconds)
% 30.86/21.31  ----------------------
% 30.86/21.32  Preprocessing        : 0.37
% 30.86/21.32  Parsing              : 0.20
% 30.86/21.32  CNF conversion       : 0.03
% 30.86/21.32  Main loop            : 20.05
% 30.86/21.32  Inferencing          : 3.64
% 30.86/21.32  Reduction            : 5.67
% 30.86/21.32  Demodulation         : 3.65
% 30.86/21.32  BG Simplification    : 0.27
% 30.86/21.32  Subsumption          : 9.01
% 30.86/21.32  Abstraction          : 0.56
% 30.86/21.32  MUC search           : 0.00
% 30.86/21.32  Cooper               : 0.00
% 30.86/21.32  Total                : 20.58
% 30.86/21.32  Index Insertion      : 0.00
% 30.86/21.32  Index Deletion       : 0.00
% 30.86/21.32  Index Matching       : 0.00
% 30.86/21.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
