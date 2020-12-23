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
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 254 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 ( 767 expanded)
%              Number of equality atoms :   34 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_60,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_361,plain,(
    ! [B_92,A_93] :
      ( v2_tops_1(B_92,A_93)
      | k1_tops_1(A_93,B_92) != k1_xboole_0
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_368,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_361])).

tff(c_376,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_368])).

tff(c_377,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_376])).

tff(c_143,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tops_1(A_71,B_72),B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_155,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_216,plain,(
    ! [A_78,B_79] :
      ( v3_pre_topc(k1_tops_1(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_221,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_216])).

tff(c_228,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_221])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_89,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_65,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_73,c_89])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_402,plain,(
    ! [A_97,A_98] :
      ( r1_tarski(A_97,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_97,A_98)
      | ~ r1_tarski(A_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_410,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_402])).

tff(c_428,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_410])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [C_49] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_49
      | ~ v3_pre_topc(C_49,'#skF_1')
      | ~ r1_tarski(C_49,'#skF_2')
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_310,plain,(
    ! [C_89] :
      ( k1_xboole_0 = C_89
      | ~ v3_pre_topc(C_89,'#skF_1')
      | ~ r1_tarski(C_89,'#skF_2')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56])).

tff(c_589,plain,(
    ! [A_108] :
      ( k1_xboole_0 = A_108
      | ~ v3_pre_topc(A_108,'#skF_1')
      | ~ r1_tarski(A_108,'#skF_2')
      | ~ r1_tarski(A_108,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_310])).

tff(c_595,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_428,c_589])).

tff(c_620,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_228,c_595])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_620])).

tff(c_623,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_624,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_628,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_40])).

tff(c_44,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_645,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_44])).

tff(c_26,plain,(
    ! [B_32,D_38,C_36,A_24] :
      ( k1_tops_1(B_32,D_38) = D_38
      | ~ v3_pre_topc(D_38,B_32)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0(B_32)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1449,plain,(
    ! [C_174,A_175] :
      ( ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_1452,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_645,c_1449])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1452])).

tff(c_1596,plain,(
    ! [B_182,D_183] :
      ( k1_tops_1(B_182,D_183) = D_183
      | ~ v3_pre_topc(D_183,B_182)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(u1_struct_0(B_182)))
      | ~ l1_pre_topc(B_182) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1599,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_645,c_1596])).

tff(c_1613,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_628,c_1599])).

tff(c_858,plain,(
    ! [A_141,B_142] :
      ( r1_tarski(k1_tops_1(A_141,B_142),B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_860,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_645,c_858])).

tff(c_871,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_860])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_892,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_871,c_2])).

tff(c_1162,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_1622,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1162])).

tff(c_1632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1622])).

tff(c_1633,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_649,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_645,c_12])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_630,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(A_111,B_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_642,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_10,c_630])).

tff(c_953,plain,(
    ! [A_143] :
      ( r1_tarski(k1_tops_1(A_143,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_10,c_858])).

tff(c_966,plain,(
    ! [A_143] :
      ( k1_tops_1(A_143,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(A_143,k1_xboole_0))
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_953,c_2])).

tff(c_979,plain,(
    ! [A_144] :
      ( k1_tops_1(A_144,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_966])).

tff(c_983,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_979])).

tff(c_1731,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_tarski(k1_tops_1(A_189,B_190),k1_tops_1(A_189,C_191))
      | ~ r1_tarski(B_190,C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1757,plain,(
    ! [B_190] :
      ( r1_tarski(k1_tops_1('#skF_1',B_190),k1_xboole_0)
      | ~ r1_tarski(B_190,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_983,c_1731])).

tff(c_1856,plain,(
    ! [B_197] :
      ( r1_tarski(k1_tops_1('#skF_1',B_197),k1_xboole_0)
      | ~ r1_tarski(B_197,k1_xboole_0)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10,c_1757])).

tff(c_1946,plain,(
    ! [A_205] :
      ( r1_tarski(k1_tops_1('#skF_1',A_205),k1_xboole_0)
      | ~ r1_tarski(A_205,k1_xboole_0)
      | ~ r1_tarski(A_205,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_1856])).

tff(c_650,plain,(
    ! [B_114,A_115] :
      ( B_114 = A_115
      | ~ r1_tarski(B_114,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_663,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_642,c_650])).

tff(c_1992,plain,(
    ! [A_206] :
      ( k1_tops_1('#skF_1',A_206) = k1_xboole_0
      | ~ r1_tarski(A_206,k1_xboole_0)
      | ~ r1_tarski(A_206,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1946,c_663])).

tff(c_2009,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_649,c_1992])).

tff(c_2026,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_2009])).

tff(c_2027,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_2026])).

tff(c_42,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_626,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_42])).

tff(c_984,plain,(
    ! [A_145,B_146] :
      ( k1_tops_1(A_145,B_146) = k1_xboole_0
      | ~ v2_tops_1(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_994,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_984])).

tff(c_1005,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_624,c_994])).

tff(c_1763,plain,(
    ! [B_190] :
      ( r1_tarski(k1_tops_1('#skF_1',B_190),k1_xboole_0)
      | ~ r1_tarski(B_190,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1731])).

tff(c_2122,plain,(
    ! [B_212] :
      ( r1_tarski(k1_tops_1('#skF_1',B_212),k1_xboole_0)
      | ~ r1_tarski(B_212,'#skF_2')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1763])).

tff(c_2125,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_645,c_2122])).

tff(c_2139,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_1633,c_2125])).

tff(c_2141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2027,c_2139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:56:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.71  
% 4.07/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.71  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.07/1.71  
% 4.07/1.71  %Foreground sorts:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Background operators:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Foreground operators:
% 4.07/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/1.71  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.07/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.07/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.71  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.07/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.07/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.07/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.71  
% 4.07/1.73  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.07/1.73  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.07/1.73  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.07/1.73  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.07/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.07/1.73  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.07/1.73  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.07/1.73  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 4.07/1.73  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.07/1.73  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.07/1.73  tff(c_38, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_60, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 4.07/1.73  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_361, plain, (![B_92, A_93]: (v2_tops_1(B_92, A_93) | k1_tops_1(A_93, B_92)!=k1_xboole_0 | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.07/1.73  tff(c_368, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_361])).
% 4.07/1.73  tff(c_376, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_368])).
% 4.07/1.73  tff(c_377, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_376])).
% 4.07/1.73  tff(c_143, plain, (![A_71, B_72]: (r1_tarski(k1_tops_1(A_71, B_72), B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.73  tff(c_148, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_143])).
% 4.07/1.73  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_148])).
% 4.07/1.73  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_216, plain, (![A_78, B_79]: (v3_pre_topc(k1_tops_1(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.07/1.73  tff(c_221, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_216])).
% 4.07/1.73  tff(c_228, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_221])).
% 4.07/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.73  tff(c_62, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.73  tff(c_73, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_62])).
% 4.07/1.73  tff(c_89, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.73  tff(c_123, plain, (![A_65]: (r1_tarski(A_65, u1_struct_0('#skF_1')) | ~r1_tarski(A_65, '#skF_2'))), inference(resolution, [status(thm)], [c_73, c_89])).
% 4.07/1.73  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.73  tff(c_402, plain, (![A_97, A_98]: (r1_tarski(A_97, u1_struct_0('#skF_1')) | ~r1_tarski(A_97, A_98) | ~r1_tarski(A_98, '#skF_2'))), inference(resolution, [status(thm)], [c_123, c_8])).
% 4.07/1.73  tff(c_410, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_155, c_402])).
% 4.07/1.73  tff(c_428, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_410])).
% 4.07/1.73  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.73  tff(c_56, plain, (![C_49]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_49 | ~v3_pre_topc(C_49, '#skF_1') | ~r1_tarski(C_49, '#skF_2') | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_310, plain, (![C_89]: (k1_xboole_0=C_89 | ~v3_pre_topc(C_89, '#skF_1') | ~r1_tarski(C_89, '#skF_2') | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_56])).
% 4.07/1.73  tff(c_589, plain, (![A_108]: (k1_xboole_0=A_108 | ~v3_pre_topc(A_108, '#skF_1') | ~r1_tarski(A_108, '#skF_2') | ~r1_tarski(A_108, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_310])).
% 4.07/1.73  tff(c_595, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_428, c_589])).
% 4.07/1.73  tff(c_620, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155, c_228, c_595])).
% 4.07/1.73  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_620])).
% 4.07/1.73  tff(c_623, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 4.07/1.73  tff(c_624, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 4.07/1.73  tff(c_40, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_628, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_40])).
% 4.07/1.73  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_645, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_44])).
% 4.07/1.73  tff(c_26, plain, (![B_32, D_38, C_36, A_24]: (k1_tops_1(B_32, D_38)=D_38 | ~v3_pre_topc(D_38, B_32) | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0(B_32))) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.07/1.73  tff(c_1449, plain, (![C_174, A_175]: (~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175))), inference(splitLeft, [status(thm)], [c_26])).
% 4.07/1.73  tff(c_1452, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_645, c_1449])).
% 4.07/1.73  tff(c_1466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1452])).
% 4.07/1.73  tff(c_1596, plain, (![B_182, D_183]: (k1_tops_1(B_182, D_183)=D_183 | ~v3_pre_topc(D_183, B_182) | ~m1_subset_1(D_183, k1_zfmisc_1(u1_struct_0(B_182))) | ~l1_pre_topc(B_182))), inference(splitRight, [status(thm)], [c_26])).
% 4.07/1.73  tff(c_1599, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_645, c_1596])).
% 4.07/1.73  tff(c_1613, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_628, c_1599])).
% 4.07/1.73  tff(c_858, plain, (![A_141, B_142]: (r1_tarski(k1_tops_1(A_141, B_142), B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.07/1.73  tff(c_860, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_645, c_858])).
% 4.07/1.73  tff(c_871, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_860])).
% 4.07/1.73  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.73  tff(c_892, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_871, c_2])).
% 4.07/1.73  tff(c_1162, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_892])).
% 4.07/1.73  tff(c_1622, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1162])).
% 4.07/1.73  tff(c_1632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1622])).
% 4.07/1.73  tff(c_1633, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_892])).
% 4.07/1.73  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.73  tff(c_649, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_645, c_12])).
% 4.07/1.73  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.73  tff(c_630, plain, (![A_111, B_112]: (r1_tarski(A_111, B_112) | ~m1_subset_1(A_111, k1_zfmisc_1(B_112)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.07/1.73  tff(c_642, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_10, c_630])).
% 4.07/1.73  tff(c_953, plain, (![A_143]: (r1_tarski(k1_tops_1(A_143, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_10, c_858])).
% 4.07/1.73  tff(c_966, plain, (![A_143]: (k1_tops_1(A_143, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tops_1(A_143, k1_xboole_0)) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_953, c_2])).
% 4.07/1.73  tff(c_979, plain, (![A_144]: (k1_tops_1(A_144, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_966])).
% 4.07/1.73  tff(c_983, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_979])).
% 4.07/1.73  tff(c_1731, plain, (![A_189, B_190, C_191]: (r1_tarski(k1_tops_1(A_189, B_190), k1_tops_1(A_189, C_191)) | ~r1_tarski(B_190, C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.07/1.73  tff(c_1757, plain, (![B_190]: (r1_tarski(k1_tops_1('#skF_1', B_190), k1_xboole_0) | ~r1_tarski(B_190, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_983, c_1731])).
% 4.07/1.73  tff(c_1856, plain, (![B_197]: (r1_tarski(k1_tops_1('#skF_1', B_197), k1_xboole_0) | ~r1_tarski(B_197, k1_xboole_0) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10, c_1757])).
% 4.07/1.73  tff(c_1946, plain, (![A_205]: (r1_tarski(k1_tops_1('#skF_1', A_205), k1_xboole_0) | ~r1_tarski(A_205, k1_xboole_0) | ~r1_tarski(A_205, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1856])).
% 4.07/1.73  tff(c_650, plain, (![B_114, A_115]: (B_114=A_115 | ~r1_tarski(B_114, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.73  tff(c_663, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_642, c_650])).
% 4.07/1.73  tff(c_1992, plain, (![A_206]: (k1_tops_1('#skF_1', A_206)=k1_xboole_0 | ~r1_tarski(A_206, k1_xboole_0) | ~r1_tarski(A_206, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1946, c_663])).
% 4.07/1.73  tff(c_2009, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_649, c_1992])).
% 4.07/1.73  tff(c_2026, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1633, c_2009])).
% 4.07/1.73  tff(c_2027, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_623, c_2026])).
% 4.07/1.73  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.07/1.73  tff(c_626, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_42])).
% 4.07/1.73  tff(c_984, plain, (![A_145, B_146]: (k1_tops_1(A_145, B_146)=k1_xboole_0 | ~v2_tops_1(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.07/1.73  tff(c_994, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_984])).
% 4.07/1.73  tff(c_1005, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_624, c_994])).
% 4.07/1.73  tff(c_1763, plain, (![B_190]: (r1_tarski(k1_tops_1('#skF_1', B_190), k1_xboole_0) | ~r1_tarski(B_190, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_1731])).
% 4.07/1.73  tff(c_2122, plain, (![B_212]: (r1_tarski(k1_tops_1('#skF_1', B_212), k1_xboole_0) | ~r1_tarski(B_212, '#skF_2') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1763])).
% 4.07/1.73  tff(c_2125, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_645, c_2122])).
% 4.07/1.73  tff(c_2139, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_626, c_1633, c_2125])).
% 4.07/1.73  tff(c_2141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2027, c_2139])).
% 4.07/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.73  
% 4.07/1.73  Inference rules
% 4.07/1.73  ----------------------
% 4.07/1.73  #Ref     : 0
% 4.07/1.73  #Sup     : 435
% 4.07/1.73  #Fact    : 0
% 4.07/1.73  #Define  : 0
% 4.07/1.73  #Split   : 20
% 4.07/1.73  #Chain   : 0
% 4.07/1.73  #Close   : 0
% 4.07/1.73  
% 4.07/1.73  Ordering : KBO
% 4.07/1.73  
% 4.07/1.73  Simplification rules
% 4.07/1.73  ----------------------
% 4.07/1.73  #Subsume      : 172
% 4.07/1.73  #Demod        : 316
% 4.07/1.73  #Tautology    : 99
% 4.07/1.73  #SimpNegUnit  : 7
% 4.07/1.73  #BackRed      : 18
% 4.07/1.73  
% 4.07/1.73  #Partial instantiations: 0
% 4.07/1.73  #Strategies tried      : 1
% 4.07/1.73  
% 4.07/1.73  Timing (in seconds)
% 4.07/1.73  ----------------------
% 4.07/1.74  Preprocessing        : 0.34
% 4.07/1.74  Parsing              : 0.17
% 4.07/1.74  CNF conversion       : 0.03
% 4.07/1.74  Main loop            : 0.62
% 4.07/1.74  Inferencing          : 0.21
% 4.07/1.74  Reduction            : 0.20
% 4.07/1.74  Demodulation         : 0.14
% 4.07/1.74  BG Simplification    : 0.03
% 4.07/1.74  Subsumption          : 0.14
% 4.07/1.74  Abstraction          : 0.03
% 4.07/1.74  MUC search           : 0.00
% 4.07/1.74  Cooper               : 0.00
% 4.07/1.74  Total                : 1.00
% 4.07/1.74  Index Insertion      : 0.00
% 4.07/1.74  Index Deletion       : 0.00
% 4.07/1.74  Index Matching       : 0.00
% 4.07/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
