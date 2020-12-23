%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:46 EST 2020

% Result     : Theorem 5.74s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 269 expanded)
%              Number of leaves         :   46 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  247 ( 752 expanded)
%              Number of equality atoms :   23 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_192,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_70,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_26,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(B_75,A_76)
      | ~ r2_hidden(B_75,A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_179,plain,(
    ! [A_93,B_94,C_95] :
      ( k9_subset_1(A_93,B_94,B_94) = B_94
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_182,plain,(
    ! [A_93,B_94] :
      ( k9_subset_1(A_93,B_94,B_94) = B_94
      | v1_xboole_0(k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_117,c_179])).

tff(c_190,plain,(
    ! [A_93,B_94] : k9_subset_1(A_93,B_94,B_94) = B_94 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_182])).

tff(c_1856,plain,(
    ! [A_231,B_232] :
      ( k2_pre_topc(A_231,B_232) = B_232
      | ~ v4_pre_topc(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1880,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1856])).

tff(c_1894,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1880])).

tff(c_1895,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1894])).

tff(c_283,plain,(
    ! [A_115,B_116] :
      ( m1_pre_topc(k1_pre_topc(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_283])).

tff(c_307,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_296])).

tff(c_38,plain,(
    ! [B_26,A_24] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_310,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_307,c_38])).

tff(c_313,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_310])).

tff(c_36,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_337,plain,(
    ! [A_122,B_123] :
      ( u1_struct_0(k1_pre_topc(A_122,B_123)) = B_123
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_355,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_337])).

tff(c_366,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_355])).

tff(c_40,plain,(
    ! [A_27] :
      ( v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | ~ v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_396,plain,
    ( v1_xboole_0('#skF_5')
    | ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5'))
    | ~ v2_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_40])).

tff(c_421,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_76,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_438,plain,(
    ! [B_132,A_133] :
      ( v1_tdlat_3(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v1_tdlat_3(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_444,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_307,c_438])).

tff(c_448,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_444])).

tff(c_449,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_448])).

tff(c_48,plain,(
    ! [B_36,A_34] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1635,plain,(
    ! [B_215,A_216] :
      ( v2_tex_2(u1_struct_0(B_215),A_216)
      | ~ v1_tdlat_3(B_215)
      | ~ m1_subset_1(u1_struct_0(B_215),k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_pre_topc(B_215,A_216)
      | v2_struct_0(B_215)
      | ~ l1_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1725,plain,(
    ! [B_218,A_219] :
      ( v2_tex_2(u1_struct_0(B_218),A_219)
      | ~ v1_tdlat_3(B_218)
      | v2_struct_0(B_218)
      | v2_struct_0(A_219)
      | ~ m1_pre_topc(B_218,A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(resolution,[status(thm)],[c_48,c_1635])).

tff(c_1743,plain,(
    ! [A_219] :
      ( v2_tex_2('#skF_5',A_219)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(A_219)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_1725])).

tff(c_1748,plain,(
    ! [A_219] :
      ( v2_tex_2('#skF_5',A_219)
      | v2_struct_0(k1_pre_topc('#skF_4','#skF_5'))
      | v2_struct_0(A_219)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_1743])).

tff(c_1750,plain,(
    ! [A_220] :
      ( v2_tex_2('#skF_5',A_220)
      | v2_struct_0(A_220)
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_220)
      | ~ l1_pre_topc(A_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_1748])).

tff(c_1753,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_307,c_1750])).

tff(c_1756,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1753])).

tff(c_1758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_1756])).

tff(c_1759,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_1768,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_1771,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_1768])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_1771])).

tff(c_1776,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_2352,plain,(
    ! [B_262,A_263] :
      ( v4_pre_topc(B_262,A_263)
      | ~ v1_xboole_0(B_262)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2396,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2352])).

tff(c_2420,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_1776,c_2396])).

tff(c_2422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1895,c_2420])).

tff(c_2423,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1894])).

tff(c_3126,plain,(
    ! [A_310,B_311] :
      ( r1_tarski('#skF_3'(A_310,B_311),B_311)
      | v2_tex_2(B_311,A_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3157,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3126])).

tff(c_3179,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_3157])).

tff(c_3180,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_3179])).

tff(c_123,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_145,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [B_79,A_78] :
      ( B_79 = A_78
      | ~ r1_tarski(B_79,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_131,c_145])).

tff(c_3194,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3180,c_150])).

tff(c_3208,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_3194])).

tff(c_3761,plain,(
    ! [A_346,B_347] :
      ( k9_subset_1(u1_struct_0(A_346),B_347,k2_pre_topc(A_346,'#skF_3'(A_346,B_347))) != '#skF_3'(A_346,B_347)
      | v2_tex_2(B_347,A_346)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3764,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4','#skF_5')) != '#skF_3'('#skF_4','#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3208,c_3761])).

tff(c_3781,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_190,c_2423,c_3208,c_3764])).

tff(c_3783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_3781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:15:26 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.74/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.16  
% 5.74/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.17  %$ v4_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 5.74/2.17  
% 5.74/2.17  %Foreground sorts:
% 5.74/2.17  
% 5.74/2.17  
% 5.74/2.17  %Background operators:
% 5.74/2.17  
% 5.74/2.17  
% 5.74/2.17  %Foreground operators:
% 5.74/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.74/2.17  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 5.74/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.74/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.74/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.74/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.74/2.17  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.74/2.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.74/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.74/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.74/2.17  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.74/2.17  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.74/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.74/2.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.74/2.17  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.74/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.74/2.17  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.74/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.74/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.74/2.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.74/2.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.74/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.74/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.74/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.74/2.17  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.74/2.17  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.74/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.74/2.17  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 5.74/2.17  
% 5.74/2.18  tff(f_207, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 5.74/2.18  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.74/2.18  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.74/2.18  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.74/2.18  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 5.74/2.18  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.74/2.18  tff(f_83, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 5.74/2.18  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.74/2.18  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.74/2.18  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 5.74/2.18  tff(f_100, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 5.74/2.18  tff(f_153, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 5.74/2.18  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.74/2.18  tff(f_173, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 5.74/2.18  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.74/2.18  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.74/2.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.74/2.18  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.74/2.18  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_70, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_26, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.74/2.18  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.74/2.18  tff(c_109, plain, (![B_75, A_76]: (m1_subset_1(B_75, A_76) | ~r2_hidden(B_75, A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.74/2.18  tff(c_117, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_109])).
% 5.74/2.18  tff(c_179, plain, (![A_93, B_94, C_95]: (k9_subset_1(A_93, B_94, B_94)=B_94 | ~m1_subset_1(C_95, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.74/2.18  tff(c_182, plain, (![A_93, B_94]: (k9_subset_1(A_93, B_94, B_94)=B_94 | v1_xboole_0(k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_117, c_179])).
% 5.74/2.18  tff(c_190, plain, (![A_93, B_94]: (k9_subset_1(A_93, B_94, B_94)=B_94)), inference(negUnitSimplification, [status(thm)], [c_26, c_182])).
% 5.74/2.18  tff(c_1856, plain, (![A_231, B_232]: (k2_pre_topc(A_231, B_232)=B_232 | ~v4_pre_topc(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.74/2.18  tff(c_1880, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1856])).
% 5.74/2.18  tff(c_1894, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1880])).
% 5.74/2.18  tff(c_1895, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1894])).
% 5.74/2.18  tff(c_283, plain, (![A_115, B_116]: (m1_pre_topc(k1_pre_topc(A_115, B_116), A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.74/2.18  tff(c_296, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_283])).
% 5.74/2.18  tff(c_307, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_296])).
% 5.74/2.18  tff(c_38, plain, (![B_26, A_24]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.18  tff(c_310, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_307, c_38])).
% 5.74/2.18  tff(c_313, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_310])).
% 5.74/2.18  tff(c_36, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.74/2.18  tff(c_337, plain, (![A_122, B_123]: (u1_struct_0(k1_pre_topc(A_122, B_123))=B_123 | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.74/2.18  tff(c_355, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_337])).
% 5.74/2.18  tff(c_366, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_355])).
% 5.74/2.18  tff(c_40, plain, (![A_27]: (v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | ~v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.74/2.18  tff(c_396, plain, (v1_xboole_0('#skF_5') | ~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | ~v2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_366, c_40])).
% 5.74/2.18  tff(c_421, plain, (~v2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_396])).
% 5.74/2.18  tff(c_76, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.74/2.18  tff(c_438, plain, (![B_132, A_133]: (v1_tdlat_3(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133) | ~v1_tdlat_3(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.74/2.18  tff(c_444, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_307, c_438])).
% 5.74/2.18  tff(c_448, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_444])).
% 5.74/2.18  tff(c_449, plain, (v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_448])).
% 5.74/2.18  tff(c_48, plain, (![B_36, A_34]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.74/2.18  tff(c_1635, plain, (![B_215, A_216]: (v2_tex_2(u1_struct_0(B_215), A_216) | ~v1_tdlat_3(B_215) | ~m1_subset_1(u1_struct_0(B_215), k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_pre_topc(B_215, A_216) | v2_struct_0(B_215) | ~l1_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.74/2.18  tff(c_1725, plain, (![B_218, A_219]: (v2_tex_2(u1_struct_0(B_218), A_219) | ~v1_tdlat_3(B_218) | v2_struct_0(B_218) | v2_struct_0(A_219) | ~m1_pre_topc(B_218, A_219) | ~l1_pre_topc(A_219))), inference(resolution, [status(thm)], [c_48, c_1635])).
% 5.74/2.18  tff(c_1743, plain, (![A_219]: (v2_tex_2('#skF_5', A_219) | ~v1_tdlat_3(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(A_219) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_219) | ~l1_pre_topc(A_219))), inference(superposition, [status(thm), theory('equality')], [c_366, c_1725])).
% 5.74/2.18  tff(c_1748, plain, (![A_219]: (v2_tex_2('#skF_5', A_219) | v2_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v2_struct_0(A_219) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_219) | ~l1_pre_topc(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_1743])).
% 5.74/2.18  tff(c_1750, plain, (![A_220]: (v2_tex_2('#skF_5', A_220) | v2_struct_0(A_220) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_220) | ~l1_pre_topc(A_220))), inference(negUnitSimplification, [status(thm)], [c_421, c_1748])).
% 5.74/2.18  tff(c_1753, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_307, c_1750])).
% 5.74/2.18  tff(c_1756, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1753])).
% 5.74/2.18  tff(c_1758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_1756])).
% 5.74/2.18  tff(c_1759, plain, (~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_396])).
% 5.74/2.18  tff(c_1768, plain, (~l1_struct_0(k1_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1759])).
% 5.74/2.18  tff(c_1771, plain, (~l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_1768])).
% 5.74/2.18  tff(c_1775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_1771])).
% 5.74/2.18  tff(c_1776, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1759])).
% 5.74/2.18  tff(c_2352, plain, (![B_262, A_263]: (v4_pre_topc(B_262, A_263) | ~v1_xboole_0(B_262) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.74/2.18  tff(c_2396, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_72, c_2352])).
% 5.74/2.18  tff(c_2420, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_1776, c_2396])).
% 5.74/2.18  tff(c_2422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1895, c_2420])).
% 5.74/2.18  tff(c_2423, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_1894])).
% 5.74/2.18  tff(c_3126, plain, (![A_310, B_311]: (r1_tarski('#skF_3'(A_310, B_311), B_311) | v2_tex_2(B_311, A_310) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.74/2.18  tff(c_3157, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_3126])).
% 5.74/2.18  tff(c_3179, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_3157])).
% 5.74/2.18  tff(c_3180, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_3179])).
% 5.74/2.18  tff(c_123, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.74/2.18  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.74/2.18  tff(c_131, plain, (![A_78, B_79]: (~v1_xboole_0(A_78) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_123, c_2])).
% 5.74/2.18  tff(c_145, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.74/2.18  tff(c_150, plain, (![B_79, A_78]: (B_79=A_78 | ~r1_tarski(B_79, A_78) | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_131, c_145])).
% 5.74/2.18  tff(c_3194, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3180, c_150])).
% 5.74/2.18  tff(c_3208, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_3194])).
% 5.74/2.18  tff(c_3761, plain, (![A_346, B_347]: (k9_subset_1(u1_struct_0(A_346), B_347, k2_pre_topc(A_346, '#skF_3'(A_346, B_347)))!='#skF_3'(A_346, B_347) | v2_tex_2(B_347, A_346) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.74/2.18  tff(c_3764, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', '#skF_5'))!='#skF_3'('#skF_4', '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3208, c_3761])).
% 5.74/2.18  tff(c_3781, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_190, c_2423, c_3208, c_3764])).
% 5.74/2.18  tff(c_3783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_3781])).
% 5.74/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.74/2.18  
% 5.74/2.18  Inference rules
% 5.74/2.18  ----------------------
% 5.74/2.18  #Ref     : 0
% 5.74/2.18  #Sup     : 835
% 5.74/2.18  #Fact    : 0
% 5.74/2.18  #Define  : 0
% 5.74/2.18  #Split   : 16
% 5.74/2.18  #Chain   : 0
% 5.74/2.18  #Close   : 0
% 5.74/2.18  
% 5.74/2.18  Ordering : KBO
% 5.74/2.18  
% 5.74/2.18  Simplification rules
% 5.74/2.18  ----------------------
% 6.00/2.18  #Subsume      : 133
% 6.00/2.18  #Demod        : 379
% 6.00/2.18  #Tautology    : 141
% 6.00/2.18  #SimpNegUnit  : 116
% 6.00/2.18  #BackRed      : 18
% 6.00/2.18  
% 6.00/2.18  #Partial instantiations: 0
% 6.00/2.18  #Strategies tried      : 1
% 6.00/2.18  
% 6.00/2.18  Timing (in seconds)
% 6.00/2.18  ----------------------
% 6.00/2.19  Preprocessing        : 0.35
% 6.00/2.19  Parsing              : 0.18
% 6.00/2.19  CNF conversion       : 0.03
% 6.00/2.19  Main loop            : 1.00
% 6.00/2.19  Inferencing          : 0.33
% 6.00/2.19  Reduction            : 0.31
% 6.00/2.19  Demodulation         : 0.20
% 6.00/2.19  BG Simplification    : 0.05
% 6.00/2.19  Subsumption          : 0.24
% 6.00/2.19  Abstraction          : 0.04
% 6.00/2.19  MUC search           : 0.00
% 6.00/2.19  Cooper               : 0.00
% 6.00/2.19  Total                : 1.39
% 6.00/2.19  Index Insertion      : 0.00
% 6.00/2.19  Index Deletion       : 0.00
% 6.00/2.19  Index Matching       : 0.00
% 6.00/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
