%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 14.04s
% Output     : CNFRefutation 14.17s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 483 expanded)
%              Number of leaves         :   37 ( 194 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 (1334 expanded)
%              Number of equality atoms :   40 ( 286 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_139,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_28,plain,(
    ! [A_37] :
      ( l1_struct_0(A_37)
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_orders_2(A_56) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_251,plain,(
    ! [A_114,B_115] :
      ( k1_orders_2(A_114,B_115) = a_2_0_orders_2(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_270,plain,(
    ! [B_115] :
      ( k1_orders_2('#skF_4',B_115) = a_2_0_orders_2('#skF_4',B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_251])).

tff(c_280,plain,(
    ! [B_115] :
      ( k1_orders_2('#skF_4',B_115) = a_2_0_orders_2('#skF_4',B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_270])).

tff(c_283,plain,(
    ! [B_116] :
      ( k1_orders_2('#skF_4',B_116) = a_2_0_orders_2('#skF_4',B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_280])).

tff(c_308,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_283])).

tff(c_42,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_309,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_42])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    ! [C_59,A_60,B_61] :
      ( r2_hidden(C_59,A_60)
      | ~ r2_hidden(C_59,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_10,A_60] :
      ( r2_hidden('#skF_1'(A_10),A_60)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(A_60))
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_29704,plain,(
    ! [A_1278,B_1279] :
      ( m1_subset_1(k1_orders_2(A_1278,B_1279),k1_zfmisc_1(u1_struct_0(A_1278)))
      | ~ m1_subset_1(B_1279,k1_zfmisc_1(u1_struct_0(A_1278)))
      | ~ l1_orders_2(A_1278)
      | ~ v5_orders_2(A_1278)
      | ~ v4_orders_2(A_1278)
      | ~ v3_orders_2(A_1278)
      | v2_struct_0(A_1278) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_29720,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_29704])).

tff(c_29733,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_53,c_75,c_75,c_29720])).

tff(c_29734,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_29733])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_29748,plain,(
    ! [A_1280] :
      ( m1_subset_1(A_1280,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_1280,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_29734,c_8])).

tff(c_29764,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_29748])).

tff(c_29770,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_29764])).

tff(c_29877,plain,(
    ! [A_1285,B_1286,C_1287] :
      ( '#skF_2'(A_1285,B_1286,C_1287) = A_1285
      | ~ r2_hidden(A_1285,a_2_0_orders_2(B_1286,C_1287))
      | ~ m1_subset_1(C_1287,k1_zfmisc_1(u1_struct_0(B_1286)))
      | ~ l1_orders_2(B_1286)
      | ~ v5_orders_2(B_1286)
      | ~ v4_orders_2(B_1286)
      | ~ v3_orders_2(B_1286)
      | v2_struct_0(B_1286) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_31108,plain,(
    ! [B_1364,C_1365] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_1364,C_1365)),B_1364,C_1365) = '#skF_1'(a_2_0_orders_2(B_1364,C_1365))
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(u1_struct_0(B_1364)))
      | ~ l1_orders_2(B_1364)
      | ~ v5_orders_2(B_1364)
      | ~ v4_orders_2(B_1364)
      | ~ v3_orders_2(B_1364)
      | v2_struct_0(B_1364)
      | a_2_0_orders_2(B_1364,C_1365) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_29877])).

tff(c_31130,plain,(
    ! [C_1365] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_1365)),'#skF_4',C_1365) = '#skF_1'(a_2_0_orders_2('#skF_4',C_1365))
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_1365) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_31108])).

tff(c_31142,plain,(
    ! [C_1365] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_1365)),'#skF_4',C_1365) = '#skF_1'(a_2_0_orders_2('#skF_4',C_1365))
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_1365) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_31130])).

tff(c_31315,plain,(
    ! [C_1375] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_1375)),'#skF_4',C_1375) = '#skF_1'(a_2_0_orders_2('#skF_4',C_1375))
      | ~ m1_subset_1(C_1375,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_1375) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_31142])).

tff(c_31346,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_31315])).

tff(c_31363,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_31346])).

tff(c_99,plain,(
    ! [A_68,A_69] :
      ( r2_hidden('#skF_1'(A_68),A_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(A_69))
      | k1_xboole_0 = A_68 ) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_106,plain,(
    ! [A_68,A_3,A_69] :
      ( r2_hidden('#skF_1'(A_68),A_3)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_68,k1_zfmisc_1(A_69))
      | k1_xboole_0 = A_68 ) ),
    inference(resolution,[status(thm)],[c_99,c_6])).

tff(c_29894,plain,(
    ! [A_1288] :
      ( r2_hidden('#skF_1'(A_1288),k2_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1288,k1_zfmisc_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | k1_xboole_0 = A_1288 ) ),
    inference(resolution,[status(thm)],[c_29734,c_106])).

tff(c_29918,plain,
    ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_29894])).

tff(c_29926,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_29918])).

tff(c_30543,plain,(
    ! [B_1321,E_1322,A_1323,C_1324] :
      ( r2_orders_2(B_1321,E_1322,'#skF_2'(A_1323,B_1321,C_1324))
      | ~ r2_hidden(E_1322,C_1324)
      | ~ m1_subset_1(E_1322,u1_struct_0(B_1321))
      | ~ r2_hidden(A_1323,a_2_0_orders_2(B_1321,C_1324))
      | ~ m1_subset_1(C_1324,k1_zfmisc_1(u1_struct_0(B_1321)))
      | ~ l1_orders_2(B_1321)
      | ~ v5_orders_2(B_1321)
      | ~ v4_orders_2(B_1321)
      | ~ v3_orders_2(B_1321)
      | v2_struct_0(B_1321) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_31209,plain,(
    ! [B_1369,E_1370,A_1371] :
      ( r2_orders_2(B_1369,E_1370,'#skF_2'(A_1371,B_1369,u1_struct_0(B_1369)))
      | ~ r2_hidden(E_1370,u1_struct_0(B_1369))
      | ~ m1_subset_1(E_1370,u1_struct_0(B_1369))
      | ~ r2_hidden(A_1371,a_2_0_orders_2(B_1369,u1_struct_0(B_1369)))
      | ~ l1_orders_2(B_1369)
      | ~ v5_orders_2(B_1369)
      | ~ v4_orders_2(B_1369)
      | ~ v3_orders_2(B_1369)
      | v2_struct_0(B_1369) ) ),
    inference(resolution,[status(thm)],[c_53,c_30543])).

tff(c_20,plain,(
    ! [A_25,C_31] :
      ( ~ r2_orders_2(A_25,C_31,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_35199,plain,(
    ! [A_1569,B_1570] :
      ( ~ r2_hidden('#skF_2'(A_1569,B_1570,u1_struct_0(B_1570)),u1_struct_0(B_1570))
      | ~ m1_subset_1('#skF_2'(A_1569,B_1570,u1_struct_0(B_1570)),u1_struct_0(B_1570))
      | ~ r2_hidden(A_1569,a_2_0_orders_2(B_1570,u1_struct_0(B_1570)))
      | ~ l1_orders_2(B_1570)
      | ~ v5_orders_2(B_1570)
      | ~ v4_orders_2(B_1570)
      | ~ v3_orders_2(B_1570)
      | v2_struct_0(B_1570) ) ),
    inference(resolution,[status(thm)],[c_31209,c_20])).

tff(c_35205,plain,(
    ! [A_1569] :
      ( ~ r2_hidden('#skF_2'(A_1569,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1569,'#skF_4',u1_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_1569,a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_35199])).

tff(c_35210,plain,(
    ! [A_1569] :
      ( ~ r2_hidden('#skF_2'(A_1569,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1569,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_1569,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_75,c_75,c_75,c_35205])).

tff(c_35327,plain,(
    ! [A_1575] :
      ( ~ r2_hidden('#skF_2'(A_1575,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_1575,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_1575,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_35210])).

tff(c_35333,plain,
    ( ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31363,c_35327])).

tff(c_35335,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29770,c_31363,c_29926,c_35333])).

tff(c_35341,plain,
    ( ~ m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_35335])).

tff(c_35348,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_35341])).

tff(c_35350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_35348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.04/6.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.04/6.49  
% 14.04/6.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.04/6.50  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 14.04/6.50  
% 14.04/6.50  %Foreground sorts:
% 14.04/6.50  
% 14.04/6.50  
% 14.04/6.50  %Background operators:
% 14.04/6.50  
% 14.04/6.50  
% 14.04/6.50  %Foreground operators:
% 14.04/6.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.04/6.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 14.04/6.50  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 14.04/6.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.04/6.50  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 14.04/6.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.04/6.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.04/6.50  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 14.04/6.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.04/6.50  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 14.04/6.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.04/6.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 14.04/6.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 14.04/6.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.04/6.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.04/6.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 14.04/6.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.04/6.50  tff('#skF_4', type, '#skF_4': $i).
% 14.04/6.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.04/6.50  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 14.04/6.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 14.04/6.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.04/6.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.04/6.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.04/6.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.04/6.50  
% 14.17/6.51  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.17/6.51  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 14.17/6.51  tff(f_153, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 14.17/6.51  tff(f_112, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 14.17/6.51  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 14.17/6.51  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 14.17/6.51  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 14.17/6.51  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 14.17/6.51  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 14.17/6.51  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 14.17/6.51  tff(f_139, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 14.17/6.51  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 14.17/6.51  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.17/6.51  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.17/6.51  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 14.17/6.51  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_28, plain, (![A_37]: (l1_struct_0(A_37) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_112])).
% 14.17/6.51  tff(c_66, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.17/6.51  tff(c_71, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_orders_2(A_56))), inference(resolution, [status(thm)], [c_28, c_66])).
% 14.17/6.51  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 14.17/6.51  tff(c_251, plain, (![A_114, B_115]: (k1_orders_2(A_114, B_115)=a_2_0_orders_2(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.17/6.51  tff(c_270, plain, (![B_115]: (k1_orders_2('#skF_4', B_115)=a_2_0_orders_2('#skF_4', B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_251])).
% 14.17/6.51  tff(c_280, plain, (![B_115]: (k1_orders_2('#skF_4', B_115)=a_2_0_orders_2('#skF_4', B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_270])).
% 14.17/6.51  tff(c_283, plain, (![B_116]: (k1_orders_2('#skF_4', B_116)=a_2_0_orders_2('#skF_4', B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_280])).
% 14.17/6.51  tff(c_308, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_283])).
% 14.17/6.51  tff(c_42, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_153])).
% 14.17/6.51  tff(c_309, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_308, c_42])).
% 14.17/6.51  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_1'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.17/6.51  tff(c_81, plain, (![C_59, A_60, B_61]: (r2_hidden(C_59, A_60) | ~r2_hidden(C_59, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.17/6.51  tff(c_84, plain, (![A_10, A_60]: (r2_hidden('#skF_1'(A_10), A_60) | ~m1_subset_1(A_10, k1_zfmisc_1(A_60)) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_10, c_81])).
% 14.17/6.51  tff(c_29704, plain, (![A_1278, B_1279]: (m1_subset_1(k1_orders_2(A_1278, B_1279), k1_zfmisc_1(u1_struct_0(A_1278))) | ~m1_subset_1(B_1279, k1_zfmisc_1(u1_struct_0(A_1278))) | ~l1_orders_2(A_1278) | ~v5_orders_2(A_1278) | ~v4_orders_2(A_1278) | ~v3_orders_2(A_1278) | v2_struct_0(A_1278))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.17/6.51  tff(c_29720, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_308, c_29704])).
% 14.17/6.51  tff(c_29733, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_53, c_75, c_75, c_29720])).
% 14.17/6.51  tff(c_29734, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_29733])).
% 14.17/6.51  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.17/6.51  tff(c_29748, plain, (![A_1280]: (m1_subset_1(A_1280, k2_struct_0('#skF_4')) | ~r2_hidden(A_1280, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_29734, c_8])).
% 14.17/6.51  tff(c_29764, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_29748])).
% 14.17/6.51  tff(c_29770, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_309, c_29764])).
% 14.17/6.51  tff(c_29877, plain, (![A_1285, B_1286, C_1287]: ('#skF_2'(A_1285, B_1286, C_1287)=A_1285 | ~r2_hidden(A_1285, a_2_0_orders_2(B_1286, C_1287)) | ~m1_subset_1(C_1287, k1_zfmisc_1(u1_struct_0(B_1286))) | ~l1_orders_2(B_1286) | ~v5_orders_2(B_1286) | ~v4_orders_2(B_1286) | ~v3_orders_2(B_1286) | v2_struct_0(B_1286))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.17/6.51  tff(c_31108, plain, (![B_1364, C_1365]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_1364, C_1365)), B_1364, C_1365)='#skF_1'(a_2_0_orders_2(B_1364, C_1365)) | ~m1_subset_1(C_1365, k1_zfmisc_1(u1_struct_0(B_1364))) | ~l1_orders_2(B_1364) | ~v5_orders_2(B_1364) | ~v4_orders_2(B_1364) | ~v3_orders_2(B_1364) | v2_struct_0(B_1364) | a_2_0_orders_2(B_1364, C_1365)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_29877])).
% 14.17/6.51  tff(c_31130, plain, (![C_1365]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_1365)), '#skF_4', C_1365)='#skF_1'(a_2_0_orders_2('#skF_4', C_1365)) | ~m1_subset_1(C_1365, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_1365)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_31108])).
% 14.17/6.51  tff(c_31142, plain, (![C_1365]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_1365)), '#skF_4', C_1365)='#skF_1'(a_2_0_orders_2('#skF_4', C_1365)) | ~m1_subset_1(C_1365, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_1365)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_31130])).
% 14.17/6.51  tff(c_31315, plain, (![C_1375]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_1375)), '#skF_4', C_1375)='#skF_1'(a_2_0_orders_2('#skF_4', C_1375)) | ~m1_subset_1(C_1375, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_1375)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_52, c_31142])).
% 14.17/6.51  tff(c_31346, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_31315])).
% 14.17/6.51  tff(c_31363, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_309, c_31346])).
% 14.17/6.51  tff(c_99, plain, (![A_68, A_69]: (r2_hidden('#skF_1'(A_68), A_69) | ~m1_subset_1(A_68, k1_zfmisc_1(A_69)) | k1_xboole_0=A_68)), inference(resolution, [status(thm)], [c_10, c_81])).
% 14.17/6.51  tff(c_6, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.17/6.51  tff(c_106, plain, (![A_68, A_3, A_69]: (r2_hidden('#skF_1'(A_68), A_3) | ~m1_subset_1(A_69, k1_zfmisc_1(A_3)) | ~m1_subset_1(A_68, k1_zfmisc_1(A_69)) | k1_xboole_0=A_68)), inference(resolution, [status(thm)], [c_99, c_6])).
% 14.17/6.51  tff(c_29894, plain, (![A_1288]: (r2_hidden('#skF_1'(A_1288), k2_struct_0('#skF_4')) | ~m1_subset_1(A_1288, k1_zfmisc_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | k1_xboole_0=A_1288)), inference(resolution, [status(thm)], [c_29734, c_106])).
% 14.17/6.51  tff(c_29918, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_29894])).
% 14.17/6.51  tff(c_29926, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_309, c_29918])).
% 14.17/6.51  tff(c_30543, plain, (![B_1321, E_1322, A_1323, C_1324]: (r2_orders_2(B_1321, E_1322, '#skF_2'(A_1323, B_1321, C_1324)) | ~r2_hidden(E_1322, C_1324) | ~m1_subset_1(E_1322, u1_struct_0(B_1321)) | ~r2_hidden(A_1323, a_2_0_orders_2(B_1321, C_1324)) | ~m1_subset_1(C_1324, k1_zfmisc_1(u1_struct_0(B_1321))) | ~l1_orders_2(B_1321) | ~v5_orders_2(B_1321) | ~v4_orders_2(B_1321) | ~v3_orders_2(B_1321) | v2_struct_0(B_1321))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.17/6.51  tff(c_31209, plain, (![B_1369, E_1370, A_1371]: (r2_orders_2(B_1369, E_1370, '#skF_2'(A_1371, B_1369, u1_struct_0(B_1369))) | ~r2_hidden(E_1370, u1_struct_0(B_1369)) | ~m1_subset_1(E_1370, u1_struct_0(B_1369)) | ~r2_hidden(A_1371, a_2_0_orders_2(B_1369, u1_struct_0(B_1369))) | ~l1_orders_2(B_1369) | ~v5_orders_2(B_1369) | ~v4_orders_2(B_1369) | ~v3_orders_2(B_1369) | v2_struct_0(B_1369))), inference(resolution, [status(thm)], [c_53, c_30543])).
% 14.17/6.51  tff(c_20, plain, (![A_25, C_31]: (~r2_orders_2(A_25, C_31, C_31) | ~m1_subset_1(C_31, u1_struct_0(A_25)) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.17/6.51  tff(c_35199, plain, (![A_1569, B_1570]: (~r2_hidden('#skF_2'(A_1569, B_1570, u1_struct_0(B_1570)), u1_struct_0(B_1570)) | ~m1_subset_1('#skF_2'(A_1569, B_1570, u1_struct_0(B_1570)), u1_struct_0(B_1570)) | ~r2_hidden(A_1569, a_2_0_orders_2(B_1570, u1_struct_0(B_1570))) | ~l1_orders_2(B_1570) | ~v5_orders_2(B_1570) | ~v4_orders_2(B_1570) | ~v3_orders_2(B_1570) | v2_struct_0(B_1570))), inference(resolution, [status(thm)], [c_31209, c_20])).
% 14.17/6.51  tff(c_35205, plain, (![A_1569]: (~r2_hidden('#skF_2'(A_1569, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_1569, '#skF_4', u1_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~r2_hidden(A_1569, a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_35199])).
% 14.17/6.51  tff(c_35210, plain, (![A_1569]: (~r2_hidden('#skF_2'(A_1569, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_1569, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_1569, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_75, c_75, c_75, c_35205])).
% 14.17/6.51  tff(c_35327, plain, (![A_1575]: (~r2_hidden('#skF_2'(A_1575, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_1575, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_1575, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_35210])).
% 14.17/6.51  tff(c_35333, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_31363, c_35327])).
% 14.17/6.51  tff(c_35335, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_29770, c_31363, c_29926, c_35333])).
% 14.17/6.51  tff(c_35341, plain, (~m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_35335])).
% 14.17/6.51  tff(c_35348, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53, c_35341])).
% 14.17/6.51  tff(c_35350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_35348])).
% 14.17/6.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.17/6.51  
% 14.17/6.51  Inference rules
% 14.17/6.51  ----------------------
% 14.17/6.51  #Ref     : 0
% 14.17/6.51  #Sup     : 7553
% 14.17/6.51  #Fact    : 0
% 14.17/6.51  #Define  : 0
% 14.17/6.51  #Split   : 48
% 14.17/6.51  #Chain   : 0
% 14.17/6.51  #Close   : 0
% 14.17/6.51  
% 14.17/6.51  Ordering : KBO
% 14.17/6.51  
% 14.17/6.51  Simplification rules
% 14.17/6.51  ----------------------
% 14.17/6.51  #Subsume      : 1100
% 14.17/6.51  #Demod        : 11206
% 14.17/6.51  #Tautology    : 1428
% 14.17/6.51  #SimpNegUnit  : 1210
% 14.17/6.51  #BackRed      : 210
% 14.17/6.51  
% 14.17/6.51  #Partial instantiations: 0
% 14.17/6.51  #Strategies tried      : 1
% 14.17/6.51  
% 14.17/6.51  Timing (in seconds)
% 14.17/6.51  ----------------------
% 14.17/6.52  Preprocessing        : 0.34
% 14.17/6.52  Parsing              : 0.18
% 14.17/6.52  CNF conversion       : 0.02
% 14.17/6.52  Main loop            : 5.37
% 14.17/6.52  Inferencing          : 1.35
% 14.17/6.52  Reduction            : 1.59
% 14.17/6.52  Demodulation         : 1.13
% 14.17/6.52  BG Simplification    : 0.17
% 14.17/6.52  Subsumption          : 1.87
% 14.17/6.52  Abstraction          : 0.26
% 14.17/6.52  MUC search           : 0.00
% 14.17/6.52  Cooper               : 0.00
% 14.17/6.52  Total                : 5.75
% 14.17/6.52  Index Insertion      : 0.00
% 14.17/6.52  Index Deletion       : 0.00
% 14.17/6.52  Index Matching       : 0.00
% 14.17/6.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
