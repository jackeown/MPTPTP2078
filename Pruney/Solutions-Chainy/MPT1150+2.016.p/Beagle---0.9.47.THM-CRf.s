%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:26 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 196 expanded)
%              Number of leaves         :   36 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  183 ( 486 expanded)
%              Number of equality atoms :   20 (  82 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_70,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_114,plain,(
    ! [A_56,B_57] :
      ( k1_orders_2(A_56,B_57) = a_2_0_orders_2(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_121,plain,(
    ! [B_57] :
      ( k1_orders_2('#skF_4',B_57) = a_2_0_orders_2('#skF_4',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_114])).

tff(c_128,plain,(
    ! [B_57] :
      ( k1_orders_2('#skF_4',B_57) = a_2_0_orders_2('#skF_4',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_121])).

tff(c_140,plain,(
    ! [B_61] :
      ( k1_orders_2('#skF_4',B_61) = a_2_0_orders_2('#skF_4',B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_128])).

tff(c_150,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_49,c_140])).

tff(c_38,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_151,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_38])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | k1_xboole_0 = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_676,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_2'(A_130,B_131,C_132),u1_struct_0(B_131))
      | ~ r2_hidden(A_130,a_2_0_orders_2(B_131,C_132))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(B_131)))
      | ~ l1_orders_2(B_131)
      | ~ v5_orders_2(B_131)
      | ~ v4_orders_2(B_131)
      | ~ v3_orders_2(B_131)
      | v2_struct_0(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_681,plain,(
    ! [A_130,C_132] :
      ( m1_subset_1('#skF_2'(A_130,'#skF_4',C_132),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',C_132))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_676])).

tff(c_684,plain,(
    ! [A_130,C_132] :
      ( m1_subset_1('#skF_2'(A_130,'#skF_4',C_132),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',C_132))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_70,c_681])).

tff(c_685,plain,(
    ! [A_130,C_132] :
      ( m1_subset_1('#skF_2'(A_130,'#skF_4',C_132),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',C_132))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_684])).

tff(c_75,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_75])).

tff(c_79,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_78])).

tff(c_80,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_83,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_886,plain,(
    ! [B_173,E_174,A_175,C_176] :
      ( r2_orders_2(B_173,E_174,'#skF_2'(A_175,B_173,C_176))
      | ~ r2_hidden(E_174,C_176)
      | ~ m1_subset_1(E_174,u1_struct_0(B_173))
      | ~ r2_hidden(A_175,a_2_0_orders_2(B_173,C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ l1_orders_2(B_173)
      | ~ v5_orders_2(B_173)
      | ~ v4_orders_2(B_173)
      | ~ v3_orders_2(B_173)
      | v2_struct_0(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_891,plain,(
    ! [E_174,A_175,C_176] :
      ( r2_orders_2('#skF_4',E_174,'#skF_2'(A_175,'#skF_4',C_176))
      | ~ r2_hidden(E_174,C_176)
      | ~ m1_subset_1(E_174,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_175,a_2_0_orders_2('#skF_4',C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_886])).

tff(c_897,plain,(
    ! [E_174,A_175,C_176] :
      ( r2_orders_2('#skF_4',E_174,'#skF_2'(A_175,'#skF_4',C_176))
      | ~ r2_hidden(E_174,C_176)
      | ~ m1_subset_1(E_174,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_175,a_2_0_orders_2('#skF_4',C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_70,c_891])).

tff(c_900,plain,(
    ! [E_177,A_178,C_179] :
      ( r2_orders_2('#skF_4',E_177,'#skF_2'(A_178,'#skF_4',C_179))
      | ~ r2_hidden(E_177,C_179)
      | ~ m1_subset_1(E_177,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_178,a_2_0_orders_2('#skF_4',C_179))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_897])).

tff(c_909,plain,(
    ! [E_180,A_181] :
      ( r2_orders_2('#skF_4',E_180,'#skF_2'(A_181,'#skF_4',k2_struct_0('#skF_4')))
      | ~ r2_hidden(E_180,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_180,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_181,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_49,c_900])).

tff(c_18,plain,(
    ! [A_10,C_16] :
      ( ~ r2_orders_2(A_10,C_16,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_917,plain,(
    ! [A_181] :
      ( ~ m1_subset_1('#skF_2'(A_181,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_181,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_181,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_181,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_909,c_18])).

tff(c_928,plain,(
    ! [A_182] :
      ( ~ r2_hidden('#skF_2'(A_182,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_182,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_182,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_917])).

tff(c_931,plain,(
    ! [A_182] :
      ( ~ r2_hidden(A_182,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_182,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_928])).

tff(c_949,plain,(
    ! [A_185] :
      ( ~ r2_hidden(A_185,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_185,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_931])).

tff(c_953,plain,(
    ! [A_130] :
      ( ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_685,c_949])).

tff(c_958,plain,(
    ! [A_186] : ~ r2_hidden(A_186,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_953])).

tff(c_962,plain,(
    ! [A_3] :
      ( a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_6,c_958])).

tff(c_972,plain,(
    ! [A_187] : ~ m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_187)) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_962])).

tff(c_977,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_49,c_972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.71  
% 3.97/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.71  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.97/1.71  
% 3.97/1.71  %Foreground sorts:
% 3.97/1.71  
% 3.97/1.71  
% 3.97/1.71  %Background operators:
% 3.97/1.71  
% 3.97/1.71  
% 3.97/1.71  %Foreground operators:
% 3.97/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.97/1.71  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.97/1.71  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.97/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.71  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 3.97/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.71  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.97/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.97/1.71  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.97/1.71  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.97/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.97/1.71  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.97/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.71  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.97/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.97/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.97/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.97/1.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.97/1.71  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.97/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.97/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.71  
% 3.97/1.73  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.97/1.73  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.97/1.73  tff(f_135, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 3.97/1.73  tff(f_94, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.97/1.73  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.97/1.73  tff(f_90, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 3.97/1.73  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.97/1.73  tff(f_121, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 3.97/1.73  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.97/1.73  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.97/1.73  tff(f_74, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.97/1.73  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.97/1.73  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.97/1.73  tff(c_49, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.97/1.73  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_46, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_44, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_42, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_40, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.97/1.73  tff(c_61, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.73  tff(c_66, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_24, c_61])).
% 3.97/1.73  tff(c_70, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_66])).
% 3.97/1.73  tff(c_114, plain, (![A_56, B_57]: (k1_orders_2(A_56, B_57)=a_2_0_orders_2(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.97/1.73  tff(c_121, plain, (![B_57]: (k1_orders_2('#skF_4', B_57)=a_2_0_orders_2('#skF_4', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_114])).
% 3.97/1.73  tff(c_128, plain, (![B_57]: (k1_orders_2('#skF_4', B_57)=a_2_0_orders_2('#skF_4', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_121])).
% 3.97/1.73  tff(c_140, plain, (![B_61]: (k1_orders_2('#skF_4', B_61)=a_2_0_orders_2('#skF_4', B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_128])).
% 3.97/1.73  tff(c_150, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_49, c_140])).
% 3.97/1.73  tff(c_38, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.97/1.73  tff(c_151, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_38])).
% 3.97/1.73  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | k1_xboole_0=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.97/1.73  tff(c_676, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_2'(A_130, B_131, C_132), u1_struct_0(B_131)) | ~r2_hidden(A_130, a_2_0_orders_2(B_131, C_132)) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(B_131))) | ~l1_orders_2(B_131) | ~v5_orders_2(B_131) | ~v4_orders_2(B_131) | ~v3_orders_2(B_131) | v2_struct_0(B_131))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.97/1.73  tff(c_681, plain, (![A_130, C_132]: (m1_subset_1('#skF_2'(A_130, '#skF_4', C_132), k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', C_132)) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_676])).
% 3.97/1.73  tff(c_684, plain, (![A_130, C_132]: (m1_subset_1('#skF_2'(A_130, '#skF_4', C_132), k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', C_132)) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_70, c_681])).
% 3.97/1.73  tff(c_685, plain, (![A_130, C_132]: (m1_subset_1('#skF_2'(A_130, '#skF_4', C_132), k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', C_132)) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_684])).
% 3.97/1.73  tff(c_75, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.73  tff(c_78, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_70, c_75])).
% 3.97/1.73  tff(c_79, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_78])).
% 3.97/1.73  tff(c_80, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_79])).
% 3.97/1.73  tff(c_83, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_24, c_80])).
% 3.97/1.73  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_83])).
% 3.97/1.73  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_79])).
% 3.97/1.73  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.97/1.73  tff(c_886, plain, (![B_173, E_174, A_175, C_176]: (r2_orders_2(B_173, E_174, '#skF_2'(A_175, B_173, C_176)) | ~r2_hidden(E_174, C_176) | ~m1_subset_1(E_174, u1_struct_0(B_173)) | ~r2_hidden(A_175, a_2_0_orders_2(B_173, C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(B_173))) | ~l1_orders_2(B_173) | ~v5_orders_2(B_173) | ~v4_orders_2(B_173) | ~v3_orders_2(B_173) | v2_struct_0(B_173))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.97/1.73  tff(c_891, plain, (![E_174, A_175, C_176]: (r2_orders_2('#skF_4', E_174, '#skF_2'(A_175, '#skF_4', C_176)) | ~r2_hidden(E_174, C_176) | ~m1_subset_1(E_174, u1_struct_0('#skF_4')) | ~r2_hidden(A_175, a_2_0_orders_2('#skF_4', C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_886])).
% 3.97/1.73  tff(c_897, plain, (![E_174, A_175, C_176]: (r2_orders_2('#skF_4', E_174, '#skF_2'(A_175, '#skF_4', C_176)) | ~r2_hidden(E_174, C_176) | ~m1_subset_1(E_174, k2_struct_0('#skF_4')) | ~r2_hidden(A_175, a_2_0_orders_2('#skF_4', C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_70, c_891])).
% 3.97/1.73  tff(c_900, plain, (![E_177, A_178, C_179]: (r2_orders_2('#skF_4', E_177, '#skF_2'(A_178, '#skF_4', C_179)) | ~r2_hidden(E_177, C_179) | ~m1_subset_1(E_177, k2_struct_0('#skF_4')) | ~r2_hidden(A_178, a_2_0_orders_2('#skF_4', C_179)) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_897])).
% 3.97/1.73  tff(c_909, plain, (![E_180, A_181]: (r2_orders_2('#skF_4', E_180, '#skF_2'(A_181, '#skF_4', k2_struct_0('#skF_4'))) | ~r2_hidden(E_180, k2_struct_0('#skF_4')) | ~m1_subset_1(E_180, k2_struct_0('#skF_4')) | ~r2_hidden(A_181, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_49, c_900])).
% 3.97/1.73  tff(c_18, plain, (![A_10, C_16]: (~r2_orders_2(A_10, C_16, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.97/1.73  tff(c_917, plain, (![A_181]: (~m1_subset_1('#skF_2'(A_181, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_181, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_181, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_181, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_909, c_18])).
% 3.97/1.73  tff(c_928, plain, (![A_182]: (~r2_hidden('#skF_2'(A_182, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_182, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_182, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_917])).
% 3.97/1.73  tff(c_931, plain, (![A_182]: (~r2_hidden(A_182, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_182, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_928])).
% 3.97/1.73  tff(c_949, plain, (![A_185]: (~r2_hidden(A_185, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_185, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_88, c_931])).
% 3.97/1.73  tff(c_953, plain, (![A_130]: (~r2_hidden(A_130, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_685, c_949])).
% 3.97/1.73  tff(c_958, plain, (![A_186]: (~r2_hidden(A_186, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_953])).
% 3.97/1.73  tff(c_962, plain, (![A_3]: (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_6, c_958])).
% 3.97/1.73  tff(c_972, plain, (![A_187]: (~m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_187)))), inference(negUnitSimplification, [status(thm)], [c_151, c_962])).
% 3.97/1.73  tff(c_977, plain, $false, inference(resolution, [status(thm)], [c_49, c_972])).
% 3.97/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.73  
% 3.97/1.73  Inference rules
% 3.97/1.73  ----------------------
% 3.97/1.73  #Ref     : 0
% 3.97/1.73  #Sup     : 173
% 3.97/1.73  #Fact    : 0
% 3.97/1.73  #Define  : 0
% 3.97/1.73  #Split   : 4
% 3.97/1.73  #Chain   : 0
% 3.97/1.73  #Close   : 0
% 3.97/1.73  
% 3.97/1.73  Ordering : KBO
% 3.97/1.73  
% 3.97/1.73  Simplification rules
% 3.97/1.73  ----------------------
% 3.97/1.73  #Subsume      : 18
% 3.97/1.73  #Demod        : 354
% 3.97/1.73  #Tautology    : 49
% 3.97/1.73  #SimpNegUnit  : 52
% 3.97/1.73  #BackRed      : 5
% 3.97/1.73  
% 3.97/1.73  #Partial instantiations: 0
% 3.97/1.73  #Strategies tried      : 1
% 3.97/1.73  
% 3.97/1.73  Timing (in seconds)
% 3.97/1.73  ----------------------
% 3.97/1.73  Preprocessing        : 0.38
% 3.97/1.73  Parsing              : 0.19
% 3.97/1.73  CNF conversion       : 0.03
% 3.97/1.73  Main loop            : 0.57
% 3.97/1.73  Inferencing          : 0.20
% 3.97/1.73  Reduction            : 0.19
% 3.97/1.73  Demodulation         : 0.13
% 3.97/1.73  BG Simplification    : 0.03
% 3.97/1.73  Subsumption          : 0.10
% 3.97/1.73  Abstraction          : 0.04
% 3.97/1.73  MUC search           : 0.00
% 3.97/1.73  Cooper               : 0.00
% 3.97/1.73  Total                : 0.98
% 3.97/1.73  Index Insertion      : 0.00
% 3.97/1.73  Index Deletion       : 0.00
% 3.97/1.73  Index Matching       : 0.00
% 3.97/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
