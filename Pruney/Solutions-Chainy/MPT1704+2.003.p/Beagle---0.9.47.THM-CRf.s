%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 9.72s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 711 expanded)
%              Number of leaves         :   46 ( 265 expanded)
%              Depth                    :   13
%              Number of atoms          :  512 (2571 expanded)
%              Number of equality atoms :   19 ( 244 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k3_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

tff(f_170,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(c_92,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_112,plain,
    ( v1_borsuk_1('#skF_4','#skF_3')
    | v1_borsuk_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_151,plain,(
    v1_borsuk_1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_104,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_150,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_96,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v1_borsuk_1('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_borsuk_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_210,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_borsuk_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_150,c_96])).

tff(c_211,plain,(
    ~ v1_borsuk_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_94,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_86,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_82,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_84,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_90,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2892,plain,(
    ! [C_230,A_231] :
      ( m1_pre_topc(C_230,A_231)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_230),u1_pre_topc(C_230)),A_231)
      | ~ l1_pre_topc(C_230)
      | ~ v2_pre_topc(C_230)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_230),u1_pre_topc(C_230)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_230),u1_pre_topc(C_230)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2901,plain,(
    ! [A_231] :
      ( m1_pre_topc('#skF_4',A_231)
      | ~ m1_pre_topc('#skF_5',A_231)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2892])).

tff(c_2907,plain,(
    ! [A_232] :
      ( m1_pre_topc('#skF_4',A_232)
      | ~ m1_pre_topc('#skF_5',A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_84,c_82,c_90,c_88,c_2901])).

tff(c_2913,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_2907])).

tff(c_2917,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2913])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_394,plain,(
    ! [B_122,A_123] :
      ( v4_pre_topc(B_122,A_123)
      | ~ v1_xboole_0(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_409,plain,(
    ! [A_123] :
      ( v4_pre_topc(k1_xboole_0,A_123)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_32,c_394])).

tff(c_415,plain,(
    ! [A_123] :
      ( v4_pre_topc(k1_xboole_0,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_409])).

tff(c_561,plain,(
    ! [B_141,A_142] :
      ( v4_pre_topc(B_141,g1_pre_topc(u1_struct_0(A_142),u1_pre_topc(A_142)))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ v4_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_564,plain,(
    ! [B_141] :
      ( v4_pre_topc(B_141,'#skF_5')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v4_pre_topc(B_141,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_561])).

tff(c_615,plain,(
    ! [B_145] :
      ( v4_pre_topc(B_145,'#skF_5')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v4_pre_topc(B_145,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_564])).

tff(c_652,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_615])).

tff(c_691,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_694,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_415,c_691])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_694])).

tff(c_700,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_22,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_subset_1(A_12)) = k2_subset_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_subset_1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_115,plain,(
    ! [A_12] : k3_subset_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_424,plain,(
    ! [A_128,B_129] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_128),B_129),A_128)
      | ~ v4_pre_topc(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_428,plain,(
    ! [A_128] :
      ( v3_pre_topc(u1_struct_0(A_128),A_128)
      | ~ v4_pre_topc(k1_xboole_0,A_128)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_424])).

tff(c_430,plain,(
    ! [A_128] :
      ( v3_pre_topc(u1_struct_0(A_128),A_128)
      | ~ v4_pre_topc(k1_xboole_0,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_428])).

tff(c_26,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_599,plain,(
    ! [B_143,A_144] :
      ( v3_pre_topc(B_143,g1_pre_topc(u1_struct_0(A_144),u1_pre_topc(A_144)))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v3_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_610,plain,(
    ! [B_143] :
      ( v3_pre_topc(B_143,'#skF_5')
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_143,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_599])).

tff(c_653,plain,(
    ! [B_146] :
      ( v3_pre_topc(B_146,'#skF_5')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_146,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_610])).

tff(c_689,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_653])).

tff(c_716,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_719,plain,
    ( ~ v4_pre_topc(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_716])).

tff(c_723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_700,c_719])).

tff(c_725,plain,(
    v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_1146,plain,(
    ! [B_174,A_175] :
      ( m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_175),u1_pre_topc(A_175)))))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ v3_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1161,plain,(
    ! [B_174] :
      ( m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_174,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1146])).

tff(c_1168,plain,(
    ! [B_176] :
      ( m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_176,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1161])).

tff(c_28,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [A_72,A_3] :
      ( r1_tarski(A_72,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_167,c_10])).

tff(c_174,plain,(
    ! [A_72,A_3] :
      ( r1_tarski(A_72,A_3)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_171])).

tff(c_1189,plain,(
    ! [B_177] :
      ( r1_tarski(B_177,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_177,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1168,c_174])).

tff(c_1209,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_1189])).

tff(c_1222,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_1209])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1238,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1222,c_4])).

tff(c_1253,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1238])).

tff(c_699,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_1266,plain,(
    ! [B_181,A_182] :
      ( v3_pre_topc(B_181,A_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)))))
      | ~ v3_pre_topc(B_181,g1_pre_topc(u1_struct_0(A_182),u1_pre_topc(A_182)))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1299,plain,(
    ! [B_181] :
      ( v3_pre_topc(B_181,'#skF_4')
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_181,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1266])).

tff(c_1310,plain,(
    ! [B_183] :
      ( v3_pre_topc(B_183,'#skF_4')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_183,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1299])).

tff(c_1349,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_1310])).

tff(c_1353,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1349])).

tff(c_1407,plain,
    ( ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_430,c_1353])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_699,c_1407])).

tff(c_1414,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1349])).

tff(c_1686,plain,(
    ! [B_193,A_194] :
      ( m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_194),u1_pre_topc(A_194)))))
      | ~ v3_pre_topc(B_193,g1_pre_topc(u1_struct_0(A_194),u1_pre_topc(A_194)))
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1719,plain,(
    ! [B_193] :
      ( m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_193,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1686])).

tff(c_1761,plain,(
    ! [B_196] :
      ( m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_196,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_1719])).

tff(c_1787,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_1761])).

tff(c_1802,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1787])).

tff(c_1827,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1802,c_174])).

tff(c_1849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_1827])).

tff(c_1850,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1238])).

tff(c_80,plain,(
    ! [B_54,A_52] :
      ( m1_subset_1(u1_struct_0(B_54),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_774,plain,(
    ! [B_150,A_151] :
      ( v4_pre_topc(u1_struct_0(B_150),A_151)
      | ~ v1_borsuk_1(B_150,A_151)
      | ~ m1_subset_1(u1_struct_0(B_150),k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_pre_topc(B_150,A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3028,plain,(
    ! [B_237,A_238] :
      ( v4_pre_topc(u1_struct_0(B_237),A_238)
      | ~ v1_borsuk_1(B_237,A_238)
      | ~ v2_pre_topc(A_238)
      | ~ m1_pre_topc(B_237,A_238)
      | ~ l1_pre_topc(A_238) ) ),
    inference(resolution,[status(thm)],[c_80,c_774])).

tff(c_3411,plain,(
    ! [A_259] :
      ( v4_pre_topc(u1_struct_0('#skF_4'),A_259)
      | ~ v1_borsuk_1('#skF_5',A_259)
      | ~ v2_pre_topc(A_259)
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_3028])).

tff(c_702,plain,(
    ! [B_147,A_148] :
      ( v1_borsuk_1(B_147,A_148)
      | ~ v4_pre_topc(u1_struct_0(B_147),A_148)
      | ~ m1_subset_1(u1_struct_0(B_147),k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m1_pre_topc(B_147,A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_714,plain,(
    ! [B_54,A_52] :
      ( v1_borsuk_1(B_54,A_52)
      | ~ v4_pre_topc(u1_struct_0(B_54),A_52)
      | ~ v2_pre_topc(A_52)
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_80,c_702])).

tff(c_5193,plain,(
    ! [A_328] :
      ( v1_borsuk_1('#skF_4',A_328)
      | ~ m1_pre_topc('#skF_4',A_328)
      | ~ v1_borsuk_1('#skF_5',A_328)
      | ~ v2_pre_topc(A_328)
      | ~ m1_pre_topc('#skF_5',A_328)
      | ~ l1_pre_topc(A_328) ) ),
    inference(resolution,[status(thm)],[c_3411,c_714])).

tff(c_5203,plain,
    ( v1_borsuk_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_5193])).

tff(c_5210,plain,(
    v1_borsuk_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_150,c_94,c_2917,c_5203])).

tff(c_5212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_5210])).

tff(c_5213,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_7895,plain,(
    ! [C_479,A_480] :
      ( m1_pre_topc(C_479,A_480)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_479),u1_pre_topc(C_479)),A_480)
      | ~ l1_pre_topc(C_479)
      | ~ v2_pre_topc(C_479)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_479),u1_pre_topc(C_479)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_479),u1_pre_topc(C_479)))
      | ~ l1_pre_topc(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_7904,plain,(
    ! [A_480] :
      ( m1_pre_topc('#skF_4',A_480)
      | ~ m1_pre_topc('#skF_5',A_480)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_480) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_7895])).

tff(c_7910,plain,(
    ! [A_481] :
      ( m1_pre_topc('#skF_4',A_481)
      | ~ m1_pre_topc('#skF_5',A_481)
      | ~ l1_pre_topc(A_481) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_84,c_82,c_90,c_88,c_7904])).

tff(c_7916,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_7910])).

tff(c_7920,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7916])).

tff(c_7922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5213,c_7920])).

tff(c_7924,plain,(
    ~ v1_borsuk_1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_110,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | v1_borsuk_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_7926,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_7924,c_110])).

tff(c_7923,plain,(
    v1_borsuk_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_8713,plain,(
    ! [B_575,A_576] :
      ( v4_pre_topc(u1_struct_0(B_575),A_576)
      | ~ v1_borsuk_1(B_575,A_576)
      | ~ m1_subset_1(u1_struct_0(B_575),k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ m1_pre_topc(B_575,A_576)
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8724,plain,(
    ! [B_54,A_52] :
      ( v4_pre_topc(u1_struct_0(B_54),A_52)
      | ~ v1_borsuk_1(B_54,A_52)
      | ~ v2_pre_topc(A_52)
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_80,c_8713])).

tff(c_8188,plain,(
    ! [B_540,A_541] :
      ( v4_pre_topc(B_540,A_541)
      | ~ v1_xboole_0(B_540)
      | ~ m1_subset_1(B_540,k1_zfmisc_1(u1_struct_0(A_541)))
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8203,plain,(
    ! [A_541] :
      ( v4_pre_topc(k1_xboole_0,A_541)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541) ) ),
    inference(resolution,[status(thm)],[c_32,c_8188])).

tff(c_8209,plain,(
    ! [A_541] :
      ( v4_pre_topc(k1_xboole_0,A_541)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8203])).

tff(c_8387,plain,(
    ! [B_558,A_559] :
      ( v4_pre_topc(B_558,g1_pre_topc(u1_struct_0(A_559),u1_pre_topc(A_559)))
      | ~ m1_subset_1(B_558,k1_zfmisc_1(u1_struct_0(A_559)))
      | ~ v4_pre_topc(B_558,A_559)
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8390,plain,(
    ! [B_558] :
      ( v4_pre_topc(B_558,'#skF_5')
      | ~ m1_subset_1(B_558,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v4_pre_topc(B_558,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8387])).

tff(c_8398,plain,(
    ! [B_561] :
      ( v4_pre_topc(B_561,'#skF_5')
      | ~ m1_subset_1(B_561,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v4_pre_topc(B_561,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_8390])).

tff(c_8435,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_8398])).

tff(c_8436,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8435])).

tff(c_8440,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8209,c_8436])).

tff(c_8444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_8440])).

tff(c_8446,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8435])).

tff(c_8223,plain,(
    ! [A_546,B_547] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_546),B_547),A_546)
      | ~ v4_pre_topc(B_547,A_546)
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8227,plain,(
    ! [A_546] :
      ( v3_pre_topc(u1_struct_0(A_546),A_546)
      | ~ v4_pre_topc(k1_xboole_0,A_546)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8223])).

tff(c_8229,plain,(
    ! [A_546] :
      ( v3_pre_topc(u1_struct_0(A_546),A_546)
      | ~ v4_pre_topc(k1_xboole_0,A_546)
      | ~ l1_pre_topc(A_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8227])).

tff(c_8454,plain,(
    ! [B_562,A_563] :
      ( v3_pre_topc(B_562,g1_pre_topc(u1_struct_0(A_563),u1_pre_topc(A_563)))
      | ~ m1_subset_1(B_562,k1_zfmisc_1(u1_struct_0(A_563)))
      | ~ v3_pre_topc(B_562,A_563)
      | ~ l1_pre_topc(A_563)
      | ~ v2_pre_topc(A_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8465,plain,(
    ! [B_562] :
      ( v3_pre_topc(B_562,'#skF_5')
      | ~ m1_subset_1(B_562,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_562,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8454])).

tff(c_8505,plain,(
    ! [B_565] :
      ( v3_pre_topc(B_565,'#skF_5')
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_565,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_8465])).

tff(c_8541,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_8505])).

tff(c_8544,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8541])).

tff(c_8547,plain,
    ( ~ v4_pre_topc(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8229,c_8544])).

tff(c_8551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8446,c_8547])).

tff(c_8553,plain,(
    v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8541])).

tff(c_8817,plain,(
    ! [B_588,A_589] :
      ( m1_subset_1(B_588,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_589),u1_pre_topc(A_589)))))
      | ~ m1_subset_1(B_588,k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ v3_pre_topc(B_588,A_589)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8832,plain,(
    ! [B_588] :
      ( m1_subset_1(B_588,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_588,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_588,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8817])).

tff(c_8839,plain,(
    ! [B_590] :
      ( m1_subset_1(B_590,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_590,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_590,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_8832])).

tff(c_7946,plain,(
    ! [A_488,B_489] :
      ( r2_hidden(A_488,B_489)
      | v1_xboole_0(B_489)
      | ~ m1_subset_1(A_488,B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7950,plain,(
    ! [A_488,A_3] :
      ( r1_tarski(A_488,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_488,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_7946,c_10])).

tff(c_7953,plain,(
    ! [A_488,A_3] :
      ( r1_tarski(A_488,A_3)
      | ~ m1_subset_1(A_488,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_7950])).

tff(c_8860,plain,(
    ! [B_591] :
      ( r1_tarski(B_591,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_591,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_591,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8839,c_7953])).

tff(c_8880,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_8860])).

tff(c_8893,plain,(
    r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8553,c_8880])).

tff(c_8909,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8893,c_4])).

tff(c_8924,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8909])).

tff(c_8445,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_8435])).

tff(c_9362,plain,(
    ! [B_610,A_611] :
      ( v3_pre_topc(B_610,A_611)
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_611),u1_pre_topc(A_611)))))
      | ~ v3_pre_topc(B_610,g1_pre_topc(u1_struct_0(A_611),u1_pre_topc(A_611)))
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9395,plain,(
    ! [B_610] :
      ( v3_pre_topc(B_610,'#skF_4')
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_610,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9362])).

tff(c_9406,plain,(
    ! [B_612] :
      ( v3_pre_topc(B_612,'#skF_4')
      | ~ m1_subset_1(B_612,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_612,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_9395])).

tff(c_9445,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_9406])).

tff(c_9449,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9445])).

tff(c_9455,plain,
    ( ~ v4_pre_topc(k1_xboole_0,'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_8229,c_9449])).

tff(c_9460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8445,c_9455])).

tff(c_9462,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_9445])).

tff(c_9806,plain,(
    ! [B_624,A_625] :
      ( m1_subset_1(B_624,k1_zfmisc_1(u1_struct_0(A_625)))
      | ~ m1_subset_1(B_624,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_625),u1_pre_topc(A_625)))))
      | ~ v3_pre_topc(B_624,g1_pre_topc(u1_struct_0(A_625),u1_pre_topc(A_625)))
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9839,plain,(
    ! [B_624] :
      ( m1_subset_1(B_624,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_624,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_624,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_9806])).

tff(c_9851,plain,(
    ! [B_626] :
      ( m1_subset_1(B_626,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_626,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_626,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_82,c_9839])).

tff(c_9877,plain,
    ( m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_9851])).

tff(c_9892,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_9877])).

tff(c_9920,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_9892,c_7953])).

tff(c_9946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8924,c_9920])).

tff(c_9947,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8909])).

tff(c_8560,plain,(
    ! [B_566,A_567] :
      ( v1_borsuk_1(B_566,A_567)
      | ~ v4_pre_topc(u1_struct_0(B_566),A_567)
      | ~ m1_subset_1(u1_struct_0(B_566),k1_zfmisc_1(u1_struct_0(A_567)))
      | ~ m1_pre_topc(B_566,A_567)
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8571,plain,(
    ! [B_54,A_52] :
      ( v1_borsuk_1(B_54,A_52)
      | ~ v4_pre_topc(u1_struct_0(B_54),A_52)
      | ~ v2_pre_topc(A_52)
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_80,c_8560])).

tff(c_11496,plain,(
    ! [A_693] :
      ( v1_borsuk_1('#skF_5',A_693)
      | ~ v4_pre_topc(u1_struct_0('#skF_4'),A_693)
      | ~ v2_pre_topc(A_693)
      | ~ m1_pre_topc('#skF_5',A_693)
      | ~ l1_pre_topc(A_693) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9947,c_8571])).

tff(c_13081,plain,(
    ! [A_751] :
      ( v1_borsuk_1('#skF_5',A_751)
      | ~ m1_pre_topc('#skF_5',A_751)
      | ~ v1_borsuk_1('#skF_4',A_751)
      | ~ v2_pre_topc(A_751)
      | ~ m1_pre_topc('#skF_4',A_751)
      | ~ l1_pre_topc(A_751) ) ),
    inference(resolution,[status(thm)],[c_8724,c_11496])).

tff(c_13091,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v1_borsuk_1('#skF_4','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_13081,c_7924])).

tff(c_13099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_7926,c_94,c_7923,c_150,c_13091])).

tff(c_13100,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_13245,plain,(
    ! [B_792,A_793] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_792),u1_pre_topc(B_792)),A_793)
      | ~ m1_pre_topc(B_792,A_793)
      | ~ l1_pre_topc(A_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_13256,plain,(
    ! [A_794] :
      ( m1_pre_topc('#skF_5',A_794)
      | ~ m1_pre_topc('#skF_4',A_794)
      | ~ l1_pre_topc(A_794) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_13245])).

tff(c_13101,plain,(
    ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_13264,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_13256,c_13101])).

tff(c_13271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13100,c_13264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:58:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.72/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.72/3.30  
% 9.72/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.72/3.30  %$ v4_pre_topc > v3_pre_topc > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > k3_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.72/3.30  
% 9.72/3.30  %Foreground sorts:
% 9.72/3.30  
% 9.72/3.30  
% 9.72/3.30  %Background operators:
% 9.72/3.30  
% 9.72/3.30  
% 9.72/3.30  %Foreground operators:
% 9.72/3.30  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.72/3.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.72/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.72/3.30  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.72/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.72/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.72/3.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.72/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.72/3.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.72/3.30  tff('#skF_5', type, '#skF_5': $i).
% 9.72/3.30  tff('#skF_3', type, '#skF_3': $i).
% 9.72/3.30  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.72/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.72/3.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.72/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.72/3.30  tff('#skF_4', type, '#skF_4': $i).
% 9.72/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.72/3.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.72/3.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 9.72/3.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.72/3.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.72/3.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.72/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.72/3.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.72/3.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.72/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.72/3.30  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 9.72/3.30  
% 10.01/3.33  tff(f_202, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tmap_1)).
% 10.01/3.33  tff(f_170, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 10.01/3.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.01/3.33  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.01/3.33  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 10.01/3.33  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_pre_topc)).
% 10.01/3.33  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 10.01/3.33  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.01/3.33  tff(f_50, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 10.01/3.33  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 10.01/3.33  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.01/3.33  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 10.01/3.33  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.01/3.33  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 10.01/3.33  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.01/3.33  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.01/3.33  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.01/3.33  tff(f_152, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 10.01/3.33  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 10.01/3.33  tff(c_92, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_112, plain, (v1_borsuk_1('#skF_4', '#skF_3') | v1_borsuk_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_151, plain, (v1_borsuk_1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_112])).
% 10.01/3.33  tff(c_104, plain, (m1_pre_topc('#skF_4', '#skF_3') | m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_150, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_104])).
% 10.01/3.33  tff(c_96, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~v1_borsuk_1('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v1_borsuk_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_210, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~v1_borsuk_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_150, c_96])).
% 10.01/3.33  tff(c_211, plain, (~v1_borsuk_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_210])).
% 10.01/3.33  tff(c_94, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_86, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_84, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_90, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_2892, plain, (![C_230, A_231]: (m1_pre_topc(C_230, A_231) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_230), u1_pre_topc(C_230)), A_231) | ~l1_pre_topc(C_230) | ~v2_pre_topc(C_230) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_230), u1_pre_topc(C_230))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_230), u1_pre_topc(C_230))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.01/3.33  tff(c_2901, plain, (![A_231]: (m1_pre_topc('#skF_4', A_231) | ~m1_pre_topc('#skF_5', A_231) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_231))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2892])).
% 10.01/3.33  tff(c_2907, plain, (![A_232]: (m1_pre_topc('#skF_4', A_232) | ~m1_pre_topc('#skF_5', A_232) | ~l1_pre_topc(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_84, c_82, c_90, c_88, c_2901])).
% 10.01/3.33  tff(c_2913, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_150, c_2907])).
% 10.01/3.33  tff(c_2917, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2913])).
% 10.01/3.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.01/3.33  tff(c_32, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.01/3.33  tff(c_394, plain, (![B_122, A_123]: (v4_pre_topc(B_122, A_123) | ~v1_xboole_0(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.01/3.33  tff(c_409, plain, (![A_123]: (v4_pre_topc(k1_xboole_0, A_123) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(resolution, [status(thm)], [c_32, c_394])).
% 10.01/3.33  tff(c_415, plain, (![A_123]: (v4_pre_topc(k1_xboole_0, A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_409])).
% 10.01/3.33  tff(c_561, plain, (![B_141, A_142]: (v4_pre_topc(B_141, g1_pre_topc(u1_struct_0(A_142), u1_pre_topc(A_142))) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~v4_pre_topc(B_141, A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.01/3.33  tff(c_564, plain, (![B_141]: (v4_pre_topc(B_141, '#skF_5') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v4_pre_topc(B_141, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_561])).
% 10.01/3.33  tff(c_615, plain, (![B_145]: (v4_pre_topc(B_145, '#skF_5') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v4_pre_topc(B_145, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_564])).
% 10.01/3.33  tff(c_652, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_32, c_615])).
% 10.01/3.33  tff(c_691, plain, (~v4_pre_topc(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_652])).
% 10.01/3.33  tff(c_694, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_415, c_691])).
% 10.01/3.33  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_694])).
% 10.01/3.33  tff(c_700, plain, (v4_pre_topc(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_652])).
% 10.01/3.33  tff(c_22, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.33  tff(c_24, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/3.33  tff(c_30, plain, (![A_12]: (k3_subset_1(A_12, k1_subset_1(A_12))=k2_subset_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.01/3.33  tff(c_114, plain, (![A_12]: (k3_subset_1(A_12, k1_subset_1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 10.01/3.33  tff(c_115, plain, (![A_12]: (k3_subset_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_114])).
% 10.01/3.33  tff(c_424, plain, (![A_128, B_129]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_128), B_129), A_128) | ~v4_pre_topc(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.01/3.33  tff(c_428, plain, (![A_128]: (v3_pre_topc(u1_struct_0(A_128), A_128) | ~v4_pre_topc(k1_xboole_0, A_128) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(superposition, [status(thm), theory('equality')], [c_115, c_424])).
% 10.01/3.33  tff(c_430, plain, (![A_128]: (v3_pre_topc(u1_struct_0(A_128), A_128) | ~v4_pre_topc(k1_xboole_0, A_128) | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_428])).
% 10.01/3.33  tff(c_26, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.33  tff(c_113, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 10.01/3.33  tff(c_599, plain, (![B_143, A_144]: (v3_pre_topc(B_143, g1_pre_topc(u1_struct_0(A_144), u1_pre_topc(A_144))) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~v3_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_610, plain, (![B_143]: (v3_pre_topc(B_143, '#skF_5') | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_143, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_599])).
% 10.01/3.33  tff(c_653, plain, (![B_146]: (v3_pre_topc(B_146, '#skF_5') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_146, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_610])).
% 10.01/3.33  tff(c_689, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_653])).
% 10.01/3.33  tff(c_716, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_689])).
% 10.01/3.33  tff(c_719, plain, (~v4_pre_topc(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_430, c_716])).
% 10.01/3.33  tff(c_723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_700, c_719])).
% 10.01/3.33  tff(c_725, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_689])).
% 10.01/3.33  tff(c_1146, plain, (![B_174, A_175]: (m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_175), u1_pre_topc(A_175))))) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~v3_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_1161, plain, (![B_174]: (m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_174, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1146])).
% 10.01/3.33  tff(c_1168, plain, (![B_176]: (m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_176, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1161])).
% 10.01/3.33  tff(c_28, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.01/3.33  tff(c_167, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | v1_xboole_0(B_73) | ~m1_subset_1(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.33  tff(c_10, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.01/3.33  tff(c_171, plain, (![A_72, A_3]: (r1_tarski(A_72, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_72, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_167, c_10])).
% 10.01/3.33  tff(c_174, plain, (![A_72, A_3]: (r1_tarski(A_72, A_3) | ~m1_subset_1(A_72, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_28, c_171])).
% 10.01/3.33  tff(c_1189, plain, (![B_177]: (r1_tarski(B_177, u1_struct_0('#skF_5')) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_177, '#skF_4'))), inference(resolution, [status(thm)], [c_1168, c_174])).
% 10.01/3.33  tff(c_1209, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_1189])).
% 10.01/3.33  tff(c_1222, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_1209])).
% 10.01/3.33  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.01/3.33  tff(c_1238, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1222, c_4])).
% 10.01/3.33  tff(c_1253, plain, (~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1238])).
% 10.01/3.33  tff(c_699, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_652])).
% 10.01/3.33  tff(c_1266, plain, (![B_181, A_182]: (v3_pre_topc(B_181, A_182) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182))))) | ~v3_pre_topc(B_181, g1_pre_topc(u1_struct_0(A_182), u1_pre_topc(A_182))) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_1299, plain, (![B_181]: (v3_pre_topc(B_181, '#skF_4') | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_181, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1266])).
% 10.01/3.33  tff(c_1310, plain, (![B_183]: (v3_pre_topc(B_183, '#skF_4') | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_183, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1299])).
% 10.01/3.33  tff(c_1349, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_1310])).
% 10.01/3.33  tff(c_1353, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1349])).
% 10.01/3.33  tff(c_1407, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_430, c_1353])).
% 10.01/3.33  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_699, c_1407])).
% 10.01/3.33  tff(c_1414, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_1349])).
% 10.01/3.33  tff(c_1686, plain, (![B_193, A_194]: (m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_194), u1_pre_topc(A_194))))) | ~v3_pre_topc(B_193, g1_pre_topc(u1_struct_0(A_194), u1_pre_topc(A_194))) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_1719, plain, (![B_193]: (m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_193, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1686])).
% 10.01/3.33  tff(c_1761, plain, (![B_196]: (m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_196, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_1719])).
% 10.01/3.33  tff(c_1787, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_1761])).
% 10.01/3.33  tff(c_1802, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1787])).
% 10.01/3.33  tff(c_1827, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1802, c_174])).
% 10.01/3.33  tff(c_1849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1253, c_1827])).
% 10.01/3.33  tff(c_1850, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1238])).
% 10.01/3.33  tff(c_80, plain, (![B_54, A_52]: (m1_subset_1(u1_struct_0(B_54), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.01/3.33  tff(c_774, plain, (![B_150, A_151]: (v4_pre_topc(u1_struct_0(B_150), A_151) | ~v1_borsuk_1(B_150, A_151) | ~m1_subset_1(u1_struct_0(B_150), k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_pre_topc(B_150, A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.01/3.33  tff(c_3028, plain, (![B_237, A_238]: (v4_pre_topc(u1_struct_0(B_237), A_238) | ~v1_borsuk_1(B_237, A_238) | ~v2_pre_topc(A_238) | ~m1_pre_topc(B_237, A_238) | ~l1_pre_topc(A_238))), inference(resolution, [status(thm)], [c_80, c_774])).
% 10.01/3.33  tff(c_3411, plain, (![A_259]: (v4_pre_topc(u1_struct_0('#skF_4'), A_259) | ~v1_borsuk_1('#skF_5', A_259) | ~v2_pre_topc(A_259) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc(A_259))), inference(superposition, [status(thm), theory('equality')], [c_1850, c_3028])).
% 10.01/3.33  tff(c_702, plain, (![B_147, A_148]: (v1_borsuk_1(B_147, A_148) | ~v4_pre_topc(u1_struct_0(B_147), A_148) | ~m1_subset_1(u1_struct_0(B_147), k1_zfmisc_1(u1_struct_0(A_148))) | ~m1_pre_topc(B_147, A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.01/3.33  tff(c_714, plain, (![B_54, A_52]: (v1_borsuk_1(B_54, A_52) | ~v4_pre_topc(u1_struct_0(B_54), A_52) | ~v2_pre_topc(A_52) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_80, c_702])).
% 10.01/3.33  tff(c_5193, plain, (![A_328]: (v1_borsuk_1('#skF_4', A_328) | ~m1_pre_topc('#skF_4', A_328) | ~v1_borsuk_1('#skF_5', A_328) | ~v2_pre_topc(A_328) | ~m1_pre_topc('#skF_5', A_328) | ~l1_pre_topc(A_328))), inference(resolution, [status(thm)], [c_3411, c_714])).
% 10.01/3.33  tff(c_5203, plain, (v1_borsuk_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_151, c_5193])).
% 10.01/3.33  tff(c_5210, plain, (v1_borsuk_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_150, c_94, c_2917, c_5203])).
% 10.01/3.33  tff(c_5212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_5210])).
% 10.01/3.33  tff(c_5213, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_210])).
% 10.01/3.33  tff(c_7895, plain, (![C_479, A_480]: (m1_pre_topc(C_479, A_480) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_479), u1_pre_topc(C_479)), A_480) | ~l1_pre_topc(C_479) | ~v2_pre_topc(C_479) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_479), u1_pre_topc(C_479))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_479), u1_pre_topc(C_479))) | ~l1_pre_topc(A_480))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.01/3.33  tff(c_7904, plain, (![A_480]: (m1_pre_topc('#skF_4', A_480) | ~m1_pre_topc('#skF_5', A_480) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_480))), inference(superposition, [status(thm), theory('equality')], [c_82, c_7895])).
% 10.01/3.33  tff(c_7910, plain, (![A_481]: (m1_pre_topc('#skF_4', A_481) | ~m1_pre_topc('#skF_5', A_481) | ~l1_pre_topc(A_481))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_84, c_82, c_90, c_88, c_7904])).
% 10.01/3.33  tff(c_7916, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_150, c_7910])).
% 10.01/3.33  tff(c_7920, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_7916])).
% 10.01/3.33  tff(c_7922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5213, c_7920])).
% 10.01/3.33  tff(c_7924, plain, (~v1_borsuk_1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_112])).
% 10.01/3.33  tff(c_110, plain, (m1_pre_topc('#skF_4', '#skF_3') | v1_borsuk_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.01/3.33  tff(c_7926, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_7924, c_110])).
% 10.01/3.33  tff(c_7923, plain, (v1_borsuk_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_112])).
% 10.01/3.33  tff(c_8713, plain, (![B_575, A_576]: (v4_pre_topc(u1_struct_0(B_575), A_576) | ~v1_borsuk_1(B_575, A_576) | ~m1_subset_1(u1_struct_0(B_575), k1_zfmisc_1(u1_struct_0(A_576))) | ~m1_pre_topc(B_575, A_576) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.01/3.33  tff(c_8724, plain, (![B_54, A_52]: (v4_pre_topc(u1_struct_0(B_54), A_52) | ~v1_borsuk_1(B_54, A_52) | ~v2_pre_topc(A_52) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_80, c_8713])).
% 10.01/3.33  tff(c_8188, plain, (![B_540, A_541]: (v4_pre_topc(B_540, A_541) | ~v1_xboole_0(B_540) | ~m1_subset_1(B_540, k1_zfmisc_1(u1_struct_0(A_541))) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.01/3.33  tff(c_8203, plain, (![A_541]: (v4_pre_topc(k1_xboole_0, A_541) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541))), inference(resolution, [status(thm)], [c_32, c_8188])).
% 10.01/3.33  tff(c_8209, plain, (![A_541]: (v4_pre_topc(k1_xboole_0, A_541) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8203])).
% 10.01/3.33  tff(c_8387, plain, (![B_558, A_559]: (v4_pre_topc(B_558, g1_pre_topc(u1_struct_0(A_559), u1_pre_topc(A_559))) | ~m1_subset_1(B_558, k1_zfmisc_1(u1_struct_0(A_559))) | ~v4_pre_topc(B_558, A_559) | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.01/3.33  tff(c_8390, plain, (![B_558]: (v4_pre_topc(B_558, '#skF_5') | ~m1_subset_1(B_558, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v4_pre_topc(B_558, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8387])).
% 10.01/3.33  tff(c_8398, plain, (![B_561]: (v4_pre_topc(B_561, '#skF_5') | ~m1_subset_1(B_561, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v4_pre_topc(B_561, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_8390])).
% 10.01/3.33  tff(c_8435, plain, (v4_pre_topc(k1_xboole_0, '#skF_5') | ~v4_pre_topc(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_32, c_8398])).
% 10.01/3.33  tff(c_8436, plain, (~v4_pre_topc(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_8435])).
% 10.01/3.33  tff(c_8440, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8209, c_8436])).
% 10.01/3.33  tff(c_8444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_8440])).
% 10.01/3.33  tff(c_8446, plain, (v4_pre_topc(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_8435])).
% 10.01/3.33  tff(c_8223, plain, (![A_546, B_547]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_546), B_547), A_546) | ~v4_pre_topc(B_547, A_546) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.01/3.33  tff(c_8227, plain, (![A_546]: (v3_pre_topc(u1_struct_0(A_546), A_546) | ~v4_pre_topc(k1_xboole_0, A_546) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(superposition, [status(thm), theory('equality')], [c_115, c_8223])).
% 10.01/3.33  tff(c_8229, plain, (![A_546]: (v3_pre_topc(u1_struct_0(A_546), A_546) | ~v4_pre_topc(k1_xboole_0, A_546) | ~l1_pre_topc(A_546))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8227])).
% 10.01/3.33  tff(c_8454, plain, (![B_562, A_563]: (v3_pre_topc(B_562, g1_pre_topc(u1_struct_0(A_563), u1_pre_topc(A_563))) | ~m1_subset_1(B_562, k1_zfmisc_1(u1_struct_0(A_563))) | ~v3_pre_topc(B_562, A_563) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_8465, plain, (![B_562]: (v3_pre_topc(B_562, '#skF_5') | ~m1_subset_1(B_562, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_562, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8454])).
% 10.01/3.33  tff(c_8505, plain, (![B_565]: (v3_pre_topc(B_565, '#skF_5') | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_565, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_8465])).
% 10.01/3.33  tff(c_8541, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_8505])).
% 10.01/3.33  tff(c_8544, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8541])).
% 10.01/3.33  tff(c_8547, plain, (~v4_pre_topc(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8229, c_8544])).
% 10.01/3.33  tff(c_8551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_8446, c_8547])).
% 10.01/3.33  tff(c_8553, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_8541])).
% 10.01/3.33  tff(c_8817, plain, (![B_588, A_589]: (m1_subset_1(B_588, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_589), u1_pre_topc(A_589))))) | ~m1_subset_1(B_588, k1_zfmisc_1(u1_struct_0(A_589))) | ~v3_pre_topc(B_588, A_589) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_8832, plain, (![B_588]: (m1_subset_1(B_588, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_588, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_588, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8817])).
% 10.01/3.33  tff(c_8839, plain, (![B_590]: (m1_subset_1(B_590, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_590, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_590, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_8832])).
% 10.01/3.33  tff(c_7946, plain, (![A_488, B_489]: (r2_hidden(A_488, B_489) | v1_xboole_0(B_489) | ~m1_subset_1(A_488, B_489))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.33  tff(c_7950, plain, (![A_488, A_3]: (r1_tarski(A_488, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_488, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_7946, c_10])).
% 10.01/3.33  tff(c_7953, plain, (![A_488, A_3]: (r1_tarski(A_488, A_3) | ~m1_subset_1(A_488, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_28, c_7950])).
% 10.01/3.33  tff(c_8860, plain, (![B_591]: (r1_tarski(B_591, u1_struct_0('#skF_5')) | ~m1_subset_1(B_591, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_591, '#skF_4'))), inference(resolution, [status(thm)], [c_8839, c_7953])).
% 10.01/3.33  tff(c_8880, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_8860])).
% 10.01/3.33  tff(c_8893, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8553, c_8880])).
% 10.01/3.33  tff(c_8909, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8893, c_4])).
% 10.01/3.33  tff(c_8924, plain, (~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_8909])).
% 10.01/3.33  tff(c_8445, plain, (v4_pre_topc(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_8435])).
% 10.01/3.33  tff(c_9362, plain, (![B_610, A_611]: (v3_pre_topc(B_610, A_611) | ~m1_subset_1(B_610, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_611), u1_pre_topc(A_611))))) | ~v3_pre_topc(B_610, g1_pre_topc(u1_struct_0(A_611), u1_pre_topc(A_611))) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_9395, plain, (![B_610]: (v3_pre_topc(B_610, '#skF_4') | ~m1_subset_1(B_610, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_610, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_9362])).
% 10.01/3.33  tff(c_9406, plain, (![B_612]: (v3_pre_topc(B_612, '#skF_4') | ~m1_subset_1(B_612, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_612, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_9395])).
% 10.01/3.33  tff(c_9445, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_9406])).
% 10.01/3.33  tff(c_9449, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_9445])).
% 10.01/3.33  tff(c_9455, plain, (~v4_pre_topc(k1_xboole_0, '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_8229, c_9449])).
% 10.01/3.33  tff(c_9460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_8445, c_9455])).
% 10.01/3.33  tff(c_9462, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_9445])).
% 10.01/3.33  tff(c_9806, plain, (![B_624, A_625]: (m1_subset_1(B_624, k1_zfmisc_1(u1_struct_0(A_625))) | ~m1_subset_1(B_624, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_625), u1_pre_topc(A_625))))) | ~v3_pre_topc(B_624, g1_pre_topc(u1_struct_0(A_625), u1_pre_topc(A_625))) | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.33  tff(c_9839, plain, (![B_624]: (m1_subset_1(B_624, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_624, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_624, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_9806])).
% 10.01/3.33  tff(c_9851, plain, (![B_626]: (m1_subset_1(B_626, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_626, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_626, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_82, c_9839])).
% 10.01/3.33  tff(c_9877, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_113, c_9851])).
% 10.01/3.33  tff(c_9892, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_9877])).
% 10.01/3.33  tff(c_9920, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_9892, c_7953])).
% 10.01/3.33  tff(c_9946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8924, c_9920])).
% 10.01/3.33  tff(c_9947, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_8909])).
% 10.01/3.33  tff(c_8560, plain, (![B_566, A_567]: (v1_borsuk_1(B_566, A_567) | ~v4_pre_topc(u1_struct_0(B_566), A_567) | ~m1_subset_1(u1_struct_0(B_566), k1_zfmisc_1(u1_struct_0(A_567))) | ~m1_pre_topc(B_566, A_567) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.01/3.33  tff(c_8571, plain, (![B_54, A_52]: (v1_borsuk_1(B_54, A_52) | ~v4_pre_topc(u1_struct_0(B_54), A_52) | ~v2_pre_topc(A_52) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_80, c_8560])).
% 10.01/3.33  tff(c_11496, plain, (![A_693]: (v1_borsuk_1('#skF_5', A_693) | ~v4_pre_topc(u1_struct_0('#skF_4'), A_693) | ~v2_pre_topc(A_693) | ~m1_pre_topc('#skF_5', A_693) | ~l1_pre_topc(A_693))), inference(superposition, [status(thm), theory('equality')], [c_9947, c_8571])).
% 10.01/3.33  tff(c_13081, plain, (![A_751]: (v1_borsuk_1('#skF_5', A_751) | ~m1_pre_topc('#skF_5', A_751) | ~v1_borsuk_1('#skF_4', A_751) | ~v2_pre_topc(A_751) | ~m1_pre_topc('#skF_4', A_751) | ~l1_pre_topc(A_751))), inference(resolution, [status(thm)], [c_8724, c_11496])).
% 10.01/3.33  tff(c_13091, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~v1_borsuk_1('#skF_4', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_13081, c_7924])).
% 10.01/3.33  tff(c_13099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_7926, c_94, c_7923, c_150, c_13091])).
% 10.01/3.33  tff(c_13100, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_104])).
% 10.01/3.33  tff(c_13245, plain, (![B_792, A_793]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_792), u1_pre_topc(B_792)), A_793) | ~m1_pre_topc(B_792, A_793) | ~l1_pre_topc(A_793))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.01/3.33  tff(c_13256, plain, (![A_794]: (m1_pre_topc('#skF_5', A_794) | ~m1_pre_topc('#skF_4', A_794) | ~l1_pre_topc(A_794))), inference(superposition, [status(thm), theory('equality')], [c_82, c_13245])).
% 10.01/3.33  tff(c_13101, plain, (~m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_104])).
% 10.01/3.33  tff(c_13264, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_13256, c_13101])).
% 10.01/3.33  tff(c_13271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_13100, c_13264])).
% 10.01/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/3.33  
% 10.01/3.33  Inference rules
% 10.01/3.33  ----------------------
% 10.01/3.33  #Ref     : 0
% 10.01/3.33  #Sup     : 2529
% 10.01/3.33  #Fact    : 0
% 10.01/3.33  #Define  : 0
% 10.01/3.33  #Split   : 63
% 10.01/3.33  #Chain   : 0
% 10.01/3.33  #Close   : 0
% 10.01/3.33  
% 10.01/3.33  Ordering : KBO
% 10.01/3.33  
% 10.01/3.33  Simplification rules
% 10.01/3.33  ----------------------
% 10.01/3.33  #Subsume      : 582
% 10.01/3.33  #Demod        : 1545
% 10.01/3.33  #Tautology    : 503
% 10.01/3.33  #SimpNegUnit  : 211
% 10.01/3.33  #BackRed      : 22
% 10.01/3.33  
% 10.01/3.33  #Partial instantiations: 0
% 10.01/3.33  #Strategies tried      : 1
% 10.01/3.33  
% 10.01/3.33  Timing (in seconds)
% 10.01/3.33  ----------------------
% 10.01/3.33  Preprocessing        : 0.38
% 10.01/3.33  Parsing              : 0.20
% 10.01/3.33  CNF conversion       : 0.03
% 10.01/3.33  Main loop            : 2.17
% 10.01/3.33  Inferencing          : 0.70
% 10.01/3.33  Reduction            : 0.71
% 10.01/3.33  Demodulation         : 0.48
% 10.01/3.33  BG Simplification    : 0.08
% 10.01/3.33  Subsumption          : 0.50
% 10.01/3.33  Abstraction          : 0.09
% 10.01/3.33  MUC search           : 0.00
% 10.01/3.33  Cooper               : 0.00
% 10.01/3.33  Total                : 2.62
% 10.01/3.33  Index Insertion      : 0.00
% 10.01/3.33  Index Deletion       : 0.00
% 10.01/3.33  Index Matching       : 0.00
% 10.01/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
