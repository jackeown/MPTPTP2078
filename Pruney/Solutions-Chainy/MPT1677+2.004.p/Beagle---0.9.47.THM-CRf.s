%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:02 EST 2020

% Result     : Theorem 9.31s
% Output     : CNFRefutation 9.70s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 241 expanded)
%              Number of leaves         :   40 ( 101 expanded)
%              Depth                    :   26
%              Number of atoms          :  409 (1539 expanded)
%              Number of equality atoms :   39 ( 167 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r2_yellow_0(A,E)
                                    & D = k2_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k2_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,B,D)
                      <=> r1_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_48,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_85,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_87,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_24,plain,(
    ! [A_18,B_25,C_26] :
      ( r2_hidden('#skF_1'(A_18,B_25,C_26),B_25)
      | r1_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_89,plain,(
    ! [A_118,C_119,B_120] :
      ( m1_subset_1(A_118,C_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(C_119))
      | ~ r2_hidden(A_118,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [A_118] :
      ( m1_subset_1(A_118,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_11] : v1_finset_1(k1_tarski(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_64,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_222,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_orders_2(A_155,B_156,B_156)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_230,plain,(
    ! [B_156] :
      ( r3_orders_2('#skF_3',B_156,B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_222])).

tff(c_242,plain,(
    ! [B_156] :
      ( r3_orders_2('#skF_3',B_156,B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_230])).

tff(c_244,plain,(
    ! [B_158] :
      ( r3_orders_2('#skF_3',B_158,B_158)
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_242])).

tff(c_258,plain,(
    ! [A_118] :
      ( r3_orders_2('#skF_3',A_118,A_118)
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_97,c_244])).

tff(c_439,plain,(
    ! [A_208,B_209,C_210] :
      ( r1_orders_2(A_208,B_209,C_210)
      | ~ r3_orders_2(A_208,B_209,C_210)
      | ~ m1_subset_1(C_210,u1_struct_0(A_208))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ l1_orders_2(A_208)
      | ~ v3_orders_2(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_453,plain,(
    ! [A_118] :
      ( r1_orders_2('#skF_3',A_118,A_118)
      | ~ m1_subset_1(A_118,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_258,c_439])).

tff(c_484,plain,(
    ! [A_118] :
      ( r1_orders_2('#skF_3',A_118,A_118)
      | ~ m1_subset_1(A_118,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_453])).

tff(c_501,plain,(
    ! [A_212] :
      ( r1_orders_2('#skF_3',A_212,A_212)
      | ~ m1_subset_1(A_212,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_212,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_484])).

tff(c_515,plain,(
    ! [A_118] :
      ( r1_orders_2('#skF_3',A_118,A_118)
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_97,c_501])).

tff(c_119,plain,(
    ! [D_132] :
      ( r2_yellow_0('#skF_3',D_132)
      | k1_xboole_0 = D_132
      | ~ m1_subset_1(D_132,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_123,plain,(
    ! [A_6] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_6))
      | k1_tarski(A_6) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_6))
      | ~ r2_hidden(A_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_126,plain,(
    ! [A_6] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_6))
      | k1_tarski(A_6) = k1_xboole_0
      | ~ r2_hidden(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_46,plain,(
    ! [A_57,C_63,B_61] :
      ( r1_lattice3(A_57,k1_tarski(C_63),B_61)
      | ~ r1_orders_2(A_57,B_61,C_63)
      | ~ m1_subset_1(C_63,u1_struct_0(A_57))
      | ~ m1_subset_1(B_61,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_32,plain,(
    ! [A_30,B_37,C_38] :
      ( m1_subset_1('#skF_2'(A_30,B_37,C_38),u1_struct_0(A_30))
      | k2_yellow_0(A_30,B_37) = C_38
      | ~ r1_lattice3(A_30,B_37,C_38)
      | ~ r2_yellow_0(A_30,B_37)
      | ~ m1_subset_1(C_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_643,plain,(
    ! [A_241,B_242,C_243] :
      ( r1_lattice3(A_241,B_242,'#skF_2'(A_241,B_242,C_243))
      | k2_yellow_0(A_241,B_242) = C_243
      | ~ r1_lattice3(A_241,B_242,C_243)
      | ~ r2_yellow_0(A_241,B_242)
      | ~ m1_subset_1(C_243,u1_struct_0(A_241))
      | ~ l1_orders_2(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    ! [A_57,B_61,C_63] :
      ( r1_orders_2(A_57,B_61,C_63)
      | ~ r1_lattice3(A_57,k1_tarski(C_63),B_61)
      | ~ m1_subset_1(C_63,u1_struct_0(A_57))
      | ~ m1_subset_1(B_61,u1_struct_0(A_57))
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1803,plain,(
    ! [A_421,C_422,C_423] :
      ( r1_orders_2(A_421,'#skF_2'(A_421,k1_tarski(C_422),C_423),C_422)
      | ~ m1_subset_1(C_422,u1_struct_0(A_421))
      | ~ m1_subset_1('#skF_2'(A_421,k1_tarski(C_422),C_423),u1_struct_0(A_421))
      | k2_yellow_0(A_421,k1_tarski(C_422)) = C_423
      | ~ r1_lattice3(A_421,k1_tarski(C_422),C_423)
      | ~ r2_yellow_0(A_421,k1_tarski(C_422))
      | ~ m1_subset_1(C_423,u1_struct_0(A_421))
      | ~ l1_orders_2(A_421) ) ),
    inference(resolution,[status(thm)],[c_643,c_48])).

tff(c_3253,plain,(
    ! [A_533,C_534,C_535] :
      ( r1_orders_2(A_533,'#skF_2'(A_533,k1_tarski(C_534),C_535),C_534)
      | ~ m1_subset_1(C_534,u1_struct_0(A_533))
      | k2_yellow_0(A_533,k1_tarski(C_534)) = C_535
      | ~ r1_lattice3(A_533,k1_tarski(C_534),C_535)
      | ~ r2_yellow_0(A_533,k1_tarski(C_534))
      | ~ m1_subset_1(C_535,u1_struct_0(A_533))
      | ~ l1_orders_2(A_533) ) ),
    inference(resolution,[status(thm)],[c_32,c_1803])).

tff(c_28,plain,(
    ! [A_30,B_37,C_38] :
      ( ~ r1_orders_2(A_30,'#skF_2'(A_30,B_37,C_38),C_38)
      | k2_yellow_0(A_30,B_37) = C_38
      | ~ r1_lattice3(A_30,B_37,C_38)
      | ~ r2_yellow_0(A_30,B_37)
      | ~ m1_subset_1(C_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3362,plain,(
    ! [A_536,C_537] :
      ( k2_yellow_0(A_536,k1_tarski(C_537)) = C_537
      | ~ r1_lattice3(A_536,k1_tarski(C_537),C_537)
      | ~ r2_yellow_0(A_536,k1_tarski(C_537))
      | ~ m1_subset_1(C_537,u1_struct_0(A_536))
      | ~ l1_orders_2(A_536) ) ),
    inference(resolution,[status(thm)],[c_3253,c_28])).

tff(c_3401,plain,(
    ! [A_538,B_539] :
      ( k2_yellow_0(A_538,k1_tarski(B_539)) = B_539
      | ~ r2_yellow_0(A_538,k1_tarski(B_539))
      | ~ r1_orders_2(A_538,B_539,B_539)
      | ~ m1_subset_1(B_539,u1_struct_0(A_538))
      | ~ l1_orders_2(A_538) ) ),
    inference(resolution,[status(thm)],[c_46,c_3362])).

tff(c_3403,plain,(
    ! [A_6] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_6)) = A_6
      | ~ r1_orders_2('#skF_3',A_6,A_6)
      | ~ m1_subset_1(A_6,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_6) = k1_xboole_0
      | ~ r2_hidden(A_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_126,c_3401])).

tff(c_3407,plain,(
    ! [A_540] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_540)) = A_540
      | ~ r1_orders_2('#skF_3',A_540,A_540)
      | ~ m1_subset_1(A_540,u1_struct_0('#skF_3'))
      | k1_tarski(A_540) = k1_xboole_0
      | ~ r2_hidden(A_540,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3403])).

tff(c_3482,plain,(
    ! [A_541] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_541)) = A_541
      | ~ m1_subset_1(A_541,u1_struct_0('#skF_3'))
      | k1_tarski(A_541) = k1_xboole_0
      | ~ r2_hidden(A_541,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_515,c_3407])).

tff(c_3515,plain,(
    ! [A_542] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_542)) = A_542
      | k1_tarski(A_542) = k1_xboole_0
      | ~ r2_hidden(A_542,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_97,c_3482])).

tff(c_52,plain,(
    ! [D_113] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_113),'#skF_5')
      | k1_xboole_0 = D_113
      | ~ m1_subset_1(D_113,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_3583,plain,(
    ! [A_542] :
      ( r2_hidden(A_542,'#skF_5')
      | k1_tarski(A_542) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(A_542),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(A_542))
      | k1_tarski(A_542) = k1_xboole_0
      | ~ r2_hidden(A_542,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3515,c_52])).

tff(c_3632,plain,(
    ! [A_547] :
      ( r2_hidden(A_547,'#skF_5')
      | ~ m1_subset_1(k1_tarski(A_547),k1_zfmisc_1('#skF_4'))
      | k1_tarski(A_547) = k1_xboole_0
      | ~ r2_hidden(A_547,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3583])).

tff(c_3638,plain,(
    ! [A_548] :
      ( r2_hidden(A_548,'#skF_5')
      | k1_tarski(A_548) = k1_xboole_0
      | ~ r2_hidden(A_548,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_3632])).

tff(c_20,plain,(
    ! [A_18,C_26,D_29,B_25] :
      ( r1_orders_2(A_18,C_26,D_29)
      | ~ r2_hidden(D_29,B_25)
      | ~ m1_subset_1(D_29,u1_struct_0(A_18))
      | ~ r1_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4007,plain,(
    ! [A_572,C_573,A_574] :
      ( r1_orders_2(A_572,C_573,A_574)
      | ~ m1_subset_1(A_574,u1_struct_0(A_572))
      | ~ r1_lattice3(A_572,'#skF_5',C_573)
      | ~ m1_subset_1(C_573,u1_struct_0(A_572))
      | ~ l1_orders_2(A_572)
      | k1_tarski(A_574) = k1_xboole_0
      | ~ r2_hidden(A_574,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3638,c_20])).

tff(c_4018,plain,(
    ! [C_573,A_118] :
      ( r1_orders_2('#skF_3',C_573,A_118)
      | ~ r1_lattice3('#skF_3','#skF_5',C_573)
      | ~ m1_subset_1(C_573,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_118) = k1_xboole_0
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_97,c_4007])).

tff(c_4033,plain,(
    ! [C_575,A_576] :
      ( r1_orders_2('#skF_3',C_575,A_576)
      | ~ r1_lattice3('#skF_3','#skF_5',C_575)
      | ~ m1_subset_1(C_575,u1_struct_0('#skF_3'))
      | k1_tarski(A_576) = k1_xboole_0
      | ~ r2_hidden(A_576,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4018])).

tff(c_4048,plain,(
    ! [A_576] :
      ( r1_orders_2('#skF_3','#skF_7',A_576)
      | ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
      | k1_tarski(A_576) = k1_xboole_0
      | ~ r2_hidden(A_576,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_4033])).

tff(c_4061,plain,(
    ! [A_577] :
      ( r1_orders_2('#skF_3','#skF_7',A_577)
      | k1_tarski(A_577) = k1_xboole_0
      | ~ r2_hidden(A_577,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4048])).

tff(c_22,plain,(
    ! [A_18,C_26,B_25] :
      ( ~ r1_orders_2(A_18,C_26,'#skF_1'(A_18,B_25,C_26))
      | r1_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4117,plain,(
    ! [B_25] :
      ( r1_lattice3('#skF_3',B_25,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_25,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_25,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4061,c_22])).

tff(c_4165,plain,(
    ! [B_578] :
      ( r1_lattice3('#skF_3',B_578,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_578,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_578,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4117])).

tff(c_4173,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4165])).

tff(c_4179,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4173])).

tff(c_4180,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_4179])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4324,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4180,c_4])).

tff(c_4359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4324])).

tff(c_4361,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_4372,plain,(
    ! [A_591,C_592,B_593] :
      ( m1_subset_1(A_591,C_592)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(C_592))
      | ~ r2_hidden(A_591,B_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4381,plain,(
    ! [A_591] :
      ( m1_subset_1(A_591,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_591,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_4372])).

tff(c_78,plain,(
    ! [D_111] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_111))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_80,plain,(
    ! [D_111] :
      ( m1_subset_1('#skF_6'(D_111),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_4360,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_26,plain,(
    ! [A_18,B_25,C_26] :
      ( m1_subset_1('#skF_1'(A_18,B_25,C_26),u1_struct_0(A_18))
      | r1_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4442,plain,(
    ! [A_609,B_610,C_611] :
      ( r2_hidden('#skF_1'(A_609,B_610,C_611),B_610)
      | r1_lattice3(A_609,B_610,C_611)
      | ~ m1_subset_1(C_611,u1_struct_0(A_609))
      | ~ l1_orders_2(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4604,plain,(
    ! [A_655,B_656,C_657,A_658] :
      ( r2_hidden('#skF_1'(A_655,B_656,C_657),A_658)
      | ~ m1_subset_1(B_656,k1_zfmisc_1(A_658))
      | r1_lattice3(A_655,B_656,C_657)
      | ~ m1_subset_1(C_657,u1_struct_0(A_655))
      | ~ l1_orders_2(A_655) ) ),
    inference(resolution,[status(thm)],[c_4442,c_6])).

tff(c_7913,plain,(
    ! [A_1037,A_1035,A_1036,C_1034,B_1038,C_1033] :
      ( r1_orders_2(A_1036,C_1033,'#skF_1'(A_1037,B_1038,C_1034))
      | ~ m1_subset_1('#skF_1'(A_1037,B_1038,C_1034),u1_struct_0(A_1036))
      | ~ r1_lattice3(A_1036,A_1035,C_1033)
      | ~ m1_subset_1(C_1033,u1_struct_0(A_1036))
      | ~ l1_orders_2(A_1036)
      | ~ m1_subset_1(B_1038,k1_zfmisc_1(A_1035))
      | r1_lattice3(A_1037,B_1038,C_1034)
      | ~ m1_subset_1(C_1034,u1_struct_0(A_1037))
      | ~ l1_orders_2(A_1037) ) ),
    inference(resolution,[status(thm)],[c_4604,c_20])).

tff(c_9065,plain,(
    ! [A_1094,C_1091,C_1095,A_1093,B_1092] :
      ( r1_orders_2(A_1093,C_1095,'#skF_1'(A_1093,B_1092,C_1091))
      | ~ r1_lattice3(A_1093,A_1094,C_1095)
      | ~ m1_subset_1(C_1095,u1_struct_0(A_1093))
      | ~ m1_subset_1(B_1092,k1_zfmisc_1(A_1094))
      | r1_lattice3(A_1093,B_1092,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0(A_1093))
      | ~ l1_orders_2(A_1093) ) ),
    inference(resolution,[status(thm)],[c_26,c_7913])).

tff(c_9105,plain,(
    ! [B_1092,C_1091] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1092,C_1091))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1092,k1_zfmisc_1('#skF_4'))
      | r1_lattice3('#skF_3',B_1092,C_1091)
      | ~ m1_subset_1(C_1091,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4360,c_9065])).

tff(c_9162,plain,(
    ! [B_1096,C_1097] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1096,C_1097))
      | ~ m1_subset_1(B_1096,k1_zfmisc_1('#skF_4'))
      | r1_lattice3('#skF_3',B_1096,C_1097)
      | ~ m1_subset_1(C_1097,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_9105])).

tff(c_9182,plain,(
    ! [B_1096] :
      ( ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(B_1096,k1_zfmisc_1('#skF_4'))
      | r1_lattice3('#skF_3',B_1096,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_9162,c_22])).

tff(c_9210,plain,(
    ! [B_1098] :
      ( ~ m1_subset_1(B_1098,k1_zfmisc_1('#skF_4'))
      | r1_lattice3('#skF_3',B_1098,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_9182])).

tff(c_9251,plain,(
    ! [D_1099] :
      ( r1_lattice3('#skF_3','#skF_6'(D_1099),'#skF_7')
      | ~ r2_hidden(D_1099,'#skF_5')
      | ~ m1_subset_1(D_1099,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_80,c_9210])).

tff(c_4412,plain,(
    ! [D_604] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_604)) = D_604
      | ~ r2_hidden(D_604,'#skF_5')
      | ~ m1_subset_1(D_604,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_4422,plain,(
    ! [A_591] :
      ( k2_yellow_0('#skF_3','#skF_6'(A_591)) = A_591
      | ~ r2_hidden(A_591,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4381,c_4412])).

tff(c_5146,plain,(
    ! [A_747,D_748,B_749] :
      ( r1_orders_2(A_747,D_748,k2_yellow_0(A_747,B_749))
      | ~ r1_lattice3(A_747,B_749,D_748)
      | ~ m1_subset_1(D_748,u1_struct_0(A_747))
      | ~ r2_yellow_0(A_747,B_749)
      | ~ m1_subset_1(k2_yellow_0(A_747,B_749),u1_struct_0(A_747))
      | ~ l1_orders_2(A_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5148,plain,(
    ! [D_748,A_591] :
      ( r1_orders_2('#skF_3',D_748,k2_yellow_0('#skF_3','#skF_6'(A_591)))
      | ~ r1_lattice3('#skF_3','#skF_6'(A_591),D_748)
      | ~ m1_subset_1(D_748,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_591))
      | ~ m1_subset_1(A_591,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_591,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4422,c_5146])).

tff(c_5671,plain,(
    ! [D_853,A_854] :
      ( r1_orders_2('#skF_3',D_853,k2_yellow_0('#skF_3','#skF_6'(A_854)))
      | ~ r1_lattice3('#skF_3','#skF_6'(A_854),D_853)
      | ~ m1_subset_1(D_853,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_854))
      | ~ m1_subset_1(A_854,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_854,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5148])).

tff(c_5682,plain,(
    ! [D_853,A_591] :
      ( r1_orders_2('#skF_3',D_853,A_591)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_591),D_853)
      | ~ m1_subset_1(D_853,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_591))
      | ~ m1_subset_1(A_591,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_591,'#skF_5')
      | ~ r2_hidden(A_591,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4422,c_5671])).

tff(c_9260,plain,(
    ! [D_1099] :
      ( r1_orders_2('#skF_3','#skF_7',D_1099)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(D_1099))
      | ~ r2_hidden(D_1099,'#skF_5')
      | ~ m1_subset_1(D_1099,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_9251,c_5682])).

tff(c_9971,plain,(
    ! [D_1114] :
      ( r1_orders_2('#skF_3','#skF_7',D_1114)
      | ~ r2_yellow_0('#skF_3','#skF_6'(D_1114))
      | ~ r2_hidden(D_1114,'#skF_5')
      | ~ m1_subset_1(D_1114,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9260])).

tff(c_10072,plain,(
    ! [D_1118] :
      ( r1_orders_2('#skF_3','#skF_7',D_1118)
      | ~ r2_hidden(D_1118,'#skF_5')
      | ~ m1_subset_1(D_1118,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_9971])).

tff(c_10105,plain,(
    ! [A_1119] :
      ( r1_orders_2('#skF_3','#skF_7',A_1119)
      | ~ r2_hidden(A_1119,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4381,c_10072])).

tff(c_10156,plain,(
    ! [B_25] :
      ( r1_lattice3('#skF_3',B_25,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_25,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10105,c_22])).

tff(c_10203,plain,(
    ! [B_1120] :
      ( r1_lattice3('#skF_3',B_1120,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1120,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_10156])).

tff(c_10218,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_10203])).

tff(c_10228,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_10218])).

tff(c_10230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4361,c_10228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.31/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.39  
% 9.60/3.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.39  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 9.60/3.39  
% 9.60/3.39  %Foreground sorts:
% 9.60/3.39  
% 9.60/3.39  
% 9.60/3.39  %Background operators:
% 9.60/3.39  
% 9.60/3.39  
% 9.60/3.39  %Foreground operators:
% 9.60/3.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.60/3.39  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 9.60/3.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.60/3.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.60/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.60/3.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.60/3.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.60/3.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.60/3.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.60/3.39  tff('#skF_7', type, '#skF_7': $i).
% 9.60/3.39  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 9.60/3.39  tff('#skF_5', type, '#skF_5': $i).
% 9.60/3.39  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 9.60/3.39  tff('#skF_3', type, '#skF_3': $i).
% 9.60/3.39  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 9.60/3.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.60/3.39  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 9.60/3.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.60/3.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.60/3.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.60/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.60/3.39  tff('#skF_4', type, '#skF_4': $i).
% 9.60/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.60/3.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.60/3.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.60/3.39  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 9.60/3.39  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.60/3.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.60/3.39  
% 9.70/3.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.70/3.41  tff(f_212, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 9.70/3.41  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 9.70/3.41  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.70/3.41  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 9.70/3.41  tff(f_48, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 9.70/3.41  tff(f_76, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 9.70/3.41  tff(f_63, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 9.70/3.41  tff(f_153, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 9.70/3.41  tff(f_108, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 9.70/3.41  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.70/3.41  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.70/3.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.70/3.41  tff(c_74, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_85, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 9.70/3.41  tff(c_68, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_87, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_68])).
% 9.70/3.41  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_24, plain, (![A_18, B_25, C_26]: (r2_hidden('#skF_1'(A_18, B_25, C_26), B_25) | r1_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.70/3.41  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_89, plain, (![A_118, C_119, B_120]: (m1_subset_1(A_118, C_119) | ~m1_subset_1(B_120, k1_zfmisc_1(C_119)) | ~r2_hidden(A_118, B_120))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.70/3.41  tff(c_97, plain, (![A_118]: (m1_subset_1(A_118, u1_struct_0('#skF_3')) | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_89])).
% 9.70/3.41  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.70/3.41  tff(c_12, plain, (![A_11]: (v1_finset_1(k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.70/3.41  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_64, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_222, plain, (![A_155, B_156, C_157]: (r3_orders_2(A_155, B_156, B_156) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.70/3.41  tff(c_230, plain, (![B_156]: (r3_orders_2('#skF_3', B_156, B_156) | ~m1_subset_1(B_156, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_222])).
% 9.70/3.41  tff(c_242, plain, (![B_156]: (r3_orders_2('#skF_3', B_156, B_156) | ~m1_subset_1(B_156, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_230])).
% 9.70/3.41  tff(c_244, plain, (![B_158]: (r3_orders_2('#skF_3', B_158, B_158) | ~m1_subset_1(B_158, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_242])).
% 9.70/3.41  tff(c_258, plain, (![A_118]: (r3_orders_2('#skF_3', A_118, A_118) | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_97, c_244])).
% 9.70/3.41  tff(c_439, plain, (![A_208, B_209, C_210]: (r1_orders_2(A_208, B_209, C_210) | ~r3_orders_2(A_208, B_209, C_210) | ~m1_subset_1(C_210, u1_struct_0(A_208)) | ~m1_subset_1(B_209, u1_struct_0(A_208)) | ~l1_orders_2(A_208) | ~v3_orders_2(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.70/3.41  tff(c_453, plain, (![A_118]: (r1_orders_2('#skF_3', A_118, A_118) | ~m1_subset_1(A_118, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_258, c_439])).
% 9.70/3.41  tff(c_484, plain, (![A_118]: (r1_orders_2('#skF_3', A_118, A_118) | ~m1_subset_1(A_118, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(A_118, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_453])).
% 9.70/3.41  tff(c_501, plain, (![A_212]: (r1_orders_2('#skF_3', A_212, A_212) | ~m1_subset_1(A_212, u1_struct_0('#skF_3')) | ~r2_hidden(A_212, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_484])).
% 9.70/3.41  tff(c_515, plain, (![A_118]: (r1_orders_2('#skF_3', A_118, A_118) | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_97, c_501])).
% 9.70/3.41  tff(c_119, plain, (![D_132]: (r2_yellow_0('#skF_3', D_132) | k1_xboole_0=D_132 | ~m1_subset_1(D_132, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_132))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_123, plain, (![A_6]: (r2_yellow_0('#skF_3', k1_tarski(A_6)) | k1_tarski(A_6)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_6)) | ~r2_hidden(A_6, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_119])).
% 9.70/3.41  tff(c_126, plain, (![A_6]: (r2_yellow_0('#skF_3', k1_tarski(A_6)) | k1_tarski(A_6)=k1_xboole_0 | ~r2_hidden(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_123])).
% 9.70/3.41  tff(c_46, plain, (![A_57, C_63, B_61]: (r1_lattice3(A_57, k1_tarski(C_63), B_61) | ~r1_orders_2(A_57, B_61, C_63) | ~m1_subset_1(C_63, u1_struct_0(A_57)) | ~m1_subset_1(B_61, u1_struct_0(A_57)) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.70/3.41  tff(c_32, plain, (![A_30, B_37, C_38]: (m1_subset_1('#skF_2'(A_30, B_37, C_38), u1_struct_0(A_30)) | k2_yellow_0(A_30, B_37)=C_38 | ~r1_lattice3(A_30, B_37, C_38) | ~r2_yellow_0(A_30, B_37) | ~m1_subset_1(C_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.70/3.41  tff(c_643, plain, (![A_241, B_242, C_243]: (r1_lattice3(A_241, B_242, '#skF_2'(A_241, B_242, C_243)) | k2_yellow_0(A_241, B_242)=C_243 | ~r1_lattice3(A_241, B_242, C_243) | ~r2_yellow_0(A_241, B_242) | ~m1_subset_1(C_243, u1_struct_0(A_241)) | ~l1_orders_2(A_241))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.70/3.41  tff(c_48, plain, (![A_57, B_61, C_63]: (r1_orders_2(A_57, B_61, C_63) | ~r1_lattice3(A_57, k1_tarski(C_63), B_61) | ~m1_subset_1(C_63, u1_struct_0(A_57)) | ~m1_subset_1(B_61, u1_struct_0(A_57)) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.70/3.41  tff(c_1803, plain, (![A_421, C_422, C_423]: (r1_orders_2(A_421, '#skF_2'(A_421, k1_tarski(C_422), C_423), C_422) | ~m1_subset_1(C_422, u1_struct_0(A_421)) | ~m1_subset_1('#skF_2'(A_421, k1_tarski(C_422), C_423), u1_struct_0(A_421)) | k2_yellow_0(A_421, k1_tarski(C_422))=C_423 | ~r1_lattice3(A_421, k1_tarski(C_422), C_423) | ~r2_yellow_0(A_421, k1_tarski(C_422)) | ~m1_subset_1(C_423, u1_struct_0(A_421)) | ~l1_orders_2(A_421))), inference(resolution, [status(thm)], [c_643, c_48])).
% 9.70/3.41  tff(c_3253, plain, (![A_533, C_534, C_535]: (r1_orders_2(A_533, '#skF_2'(A_533, k1_tarski(C_534), C_535), C_534) | ~m1_subset_1(C_534, u1_struct_0(A_533)) | k2_yellow_0(A_533, k1_tarski(C_534))=C_535 | ~r1_lattice3(A_533, k1_tarski(C_534), C_535) | ~r2_yellow_0(A_533, k1_tarski(C_534)) | ~m1_subset_1(C_535, u1_struct_0(A_533)) | ~l1_orders_2(A_533))), inference(resolution, [status(thm)], [c_32, c_1803])).
% 9.70/3.41  tff(c_28, plain, (![A_30, B_37, C_38]: (~r1_orders_2(A_30, '#skF_2'(A_30, B_37, C_38), C_38) | k2_yellow_0(A_30, B_37)=C_38 | ~r1_lattice3(A_30, B_37, C_38) | ~r2_yellow_0(A_30, B_37) | ~m1_subset_1(C_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.70/3.41  tff(c_3362, plain, (![A_536, C_537]: (k2_yellow_0(A_536, k1_tarski(C_537))=C_537 | ~r1_lattice3(A_536, k1_tarski(C_537), C_537) | ~r2_yellow_0(A_536, k1_tarski(C_537)) | ~m1_subset_1(C_537, u1_struct_0(A_536)) | ~l1_orders_2(A_536))), inference(resolution, [status(thm)], [c_3253, c_28])).
% 9.70/3.41  tff(c_3401, plain, (![A_538, B_539]: (k2_yellow_0(A_538, k1_tarski(B_539))=B_539 | ~r2_yellow_0(A_538, k1_tarski(B_539)) | ~r1_orders_2(A_538, B_539, B_539) | ~m1_subset_1(B_539, u1_struct_0(A_538)) | ~l1_orders_2(A_538))), inference(resolution, [status(thm)], [c_46, c_3362])).
% 9.70/3.41  tff(c_3403, plain, (![A_6]: (k2_yellow_0('#skF_3', k1_tarski(A_6))=A_6 | ~r1_orders_2('#skF_3', A_6, A_6) | ~m1_subset_1(A_6, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_6)=k1_xboole_0 | ~r2_hidden(A_6, '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_3401])).
% 9.70/3.41  tff(c_3407, plain, (![A_540]: (k2_yellow_0('#skF_3', k1_tarski(A_540))=A_540 | ~r1_orders_2('#skF_3', A_540, A_540) | ~m1_subset_1(A_540, u1_struct_0('#skF_3')) | k1_tarski(A_540)=k1_xboole_0 | ~r2_hidden(A_540, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3403])).
% 9.70/3.41  tff(c_3482, plain, (![A_541]: (k2_yellow_0('#skF_3', k1_tarski(A_541))=A_541 | ~m1_subset_1(A_541, u1_struct_0('#skF_3')) | k1_tarski(A_541)=k1_xboole_0 | ~r2_hidden(A_541, '#skF_4'))), inference(resolution, [status(thm)], [c_515, c_3407])).
% 9.70/3.41  tff(c_3515, plain, (![A_542]: (k2_yellow_0('#skF_3', k1_tarski(A_542))=A_542 | k1_tarski(A_542)=k1_xboole_0 | ~r2_hidden(A_542, '#skF_4'))), inference(resolution, [status(thm)], [c_97, c_3482])).
% 9.70/3.41  tff(c_52, plain, (![D_113]: (r2_hidden(k2_yellow_0('#skF_3', D_113), '#skF_5') | k1_xboole_0=D_113 | ~m1_subset_1(D_113, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_113))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_3583, plain, (![A_542]: (r2_hidden(A_542, '#skF_5') | k1_tarski(A_542)=k1_xboole_0 | ~m1_subset_1(k1_tarski(A_542), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski(A_542)) | k1_tarski(A_542)=k1_xboole_0 | ~r2_hidden(A_542, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3515, c_52])).
% 9.70/3.41  tff(c_3632, plain, (![A_547]: (r2_hidden(A_547, '#skF_5') | ~m1_subset_1(k1_tarski(A_547), k1_zfmisc_1('#skF_4')) | k1_tarski(A_547)=k1_xboole_0 | ~r2_hidden(A_547, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3583])).
% 9.70/3.41  tff(c_3638, plain, (![A_548]: (r2_hidden(A_548, '#skF_5') | k1_tarski(A_548)=k1_xboole_0 | ~r2_hidden(A_548, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_3632])).
% 9.70/3.41  tff(c_20, plain, (![A_18, C_26, D_29, B_25]: (r1_orders_2(A_18, C_26, D_29) | ~r2_hidden(D_29, B_25) | ~m1_subset_1(D_29, u1_struct_0(A_18)) | ~r1_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.70/3.41  tff(c_4007, plain, (![A_572, C_573, A_574]: (r1_orders_2(A_572, C_573, A_574) | ~m1_subset_1(A_574, u1_struct_0(A_572)) | ~r1_lattice3(A_572, '#skF_5', C_573) | ~m1_subset_1(C_573, u1_struct_0(A_572)) | ~l1_orders_2(A_572) | k1_tarski(A_574)=k1_xboole_0 | ~r2_hidden(A_574, '#skF_4'))), inference(resolution, [status(thm)], [c_3638, c_20])).
% 9.70/3.41  tff(c_4018, plain, (![C_573, A_118]: (r1_orders_2('#skF_3', C_573, A_118) | ~r1_lattice3('#skF_3', '#skF_5', C_573) | ~m1_subset_1(C_573, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_118)=k1_xboole_0 | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_97, c_4007])).
% 9.70/3.41  tff(c_4033, plain, (![C_575, A_576]: (r1_orders_2('#skF_3', C_575, A_576) | ~r1_lattice3('#skF_3', '#skF_5', C_575) | ~m1_subset_1(C_575, u1_struct_0('#skF_3')) | k1_tarski(A_576)=k1_xboole_0 | ~r2_hidden(A_576, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4018])).
% 9.70/3.41  tff(c_4048, plain, (![A_576]: (r1_orders_2('#skF_3', '#skF_7', A_576) | ~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | k1_tarski(A_576)=k1_xboole_0 | ~r2_hidden(A_576, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_4033])).
% 9.70/3.41  tff(c_4061, plain, (![A_577]: (r1_orders_2('#skF_3', '#skF_7', A_577) | k1_tarski(A_577)=k1_xboole_0 | ~r2_hidden(A_577, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4048])).
% 9.70/3.41  tff(c_22, plain, (![A_18, C_26, B_25]: (~r1_orders_2(A_18, C_26, '#skF_1'(A_18, B_25, C_26)) | r1_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.70/3.41  tff(c_4117, plain, (![B_25]: (r1_lattice3('#skF_3', B_25, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_25, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_25, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_4061, c_22])).
% 9.70/3.41  tff(c_4165, plain, (![B_578]: (r1_lattice3('#skF_3', B_578, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_578, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_578, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4117])).
% 9.70/3.41  tff(c_4173, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_4165])).
% 9.70/3.41  tff(c_4179, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4173])).
% 9.70/3.41  tff(c_4180, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_87, c_4179])).
% 9.70/3.41  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.70/3.41  tff(c_4324, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4180, c_4])).
% 9.70/3.41  tff(c_4359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4324])).
% 9.70/3.41  tff(c_4361, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 9.70/3.41  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_4372, plain, (![A_591, C_592, B_593]: (m1_subset_1(A_591, C_592) | ~m1_subset_1(B_593, k1_zfmisc_1(C_592)) | ~r2_hidden(A_591, B_593))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.70/3.41  tff(c_4381, plain, (![A_591]: (m1_subset_1(A_591, u1_struct_0('#skF_3')) | ~r2_hidden(A_591, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_4372])).
% 9.70/3.41  tff(c_78, plain, (![D_111]: (r2_yellow_0('#skF_3', '#skF_6'(D_111)) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_80, plain, (![D_111]: (m1_subset_1('#skF_6'(D_111), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_4360, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 9.70/3.41  tff(c_26, plain, (![A_18, B_25, C_26]: (m1_subset_1('#skF_1'(A_18, B_25, C_26), u1_struct_0(A_18)) | r1_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.70/3.41  tff(c_4442, plain, (![A_609, B_610, C_611]: (r2_hidden('#skF_1'(A_609, B_610, C_611), B_610) | r1_lattice3(A_609, B_610, C_611) | ~m1_subset_1(C_611, u1_struct_0(A_609)) | ~l1_orders_2(A_609))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.70/3.41  tff(c_6, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.70/3.41  tff(c_4604, plain, (![A_655, B_656, C_657, A_658]: (r2_hidden('#skF_1'(A_655, B_656, C_657), A_658) | ~m1_subset_1(B_656, k1_zfmisc_1(A_658)) | r1_lattice3(A_655, B_656, C_657) | ~m1_subset_1(C_657, u1_struct_0(A_655)) | ~l1_orders_2(A_655))), inference(resolution, [status(thm)], [c_4442, c_6])).
% 9.70/3.41  tff(c_7913, plain, (![A_1037, A_1035, A_1036, C_1034, B_1038, C_1033]: (r1_orders_2(A_1036, C_1033, '#skF_1'(A_1037, B_1038, C_1034)) | ~m1_subset_1('#skF_1'(A_1037, B_1038, C_1034), u1_struct_0(A_1036)) | ~r1_lattice3(A_1036, A_1035, C_1033) | ~m1_subset_1(C_1033, u1_struct_0(A_1036)) | ~l1_orders_2(A_1036) | ~m1_subset_1(B_1038, k1_zfmisc_1(A_1035)) | r1_lattice3(A_1037, B_1038, C_1034) | ~m1_subset_1(C_1034, u1_struct_0(A_1037)) | ~l1_orders_2(A_1037))), inference(resolution, [status(thm)], [c_4604, c_20])).
% 9.70/3.41  tff(c_9065, plain, (![A_1094, C_1091, C_1095, A_1093, B_1092]: (r1_orders_2(A_1093, C_1095, '#skF_1'(A_1093, B_1092, C_1091)) | ~r1_lattice3(A_1093, A_1094, C_1095) | ~m1_subset_1(C_1095, u1_struct_0(A_1093)) | ~m1_subset_1(B_1092, k1_zfmisc_1(A_1094)) | r1_lattice3(A_1093, B_1092, C_1091) | ~m1_subset_1(C_1091, u1_struct_0(A_1093)) | ~l1_orders_2(A_1093))), inference(resolution, [status(thm)], [c_26, c_7913])).
% 9.70/3.41  tff(c_9105, plain, (![B_1092, C_1091]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1092, C_1091)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~m1_subset_1(B_1092, k1_zfmisc_1('#skF_4')) | r1_lattice3('#skF_3', B_1092, C_1091) | ~m1_subset_1(C_1091, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_4360, c_9065])).
% 9.70/3.41  tff(c_9162, plain, (![B_1096, C_1097]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1096, C_1097)) | ~m1_subset_1(B_1096, k1_zfmisc_1('#skF_4')) | r1_lattice3('#skF_3', B_1096, C_1097) | ~m1_subset_1(C_1097, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_9105])).
% 9.70/3.41  tff(c_9182, plain, (![B_1096]: (~l1_orders_2('#skF_3') | ~m1_subset_1(B_1096, k1_zfmisc_1('#skF_4')) | r1_lattice3('#skF_3', B_1096, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_9162, c_22])).
% 9.70/3.41  tff(c_9210, plain, (![B_1098]: (~m1_subset_1(B_1098, k1_zfmisc_1('#skF_4')) | r1_lattice3('#skF_3', B_1098, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_9182])).
% 9.70/3.41  tff(c_9251, plain, (![D_1099]: (r1_lattice3('#skF_3', '#skF_6'(D_1099), '#skF_7') | ~r2_hidden(D_1099, '#skF_5') | ~m1_subset_1(D_1099, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_80, c_9210])).
% 9.70/3.41  tff(c_4412, plain, (![D_604]: (k2_yellow_0('#skF_3', '#skF_6'(D_604))=D_604 | ~r2_hidden(D_604, '#skF_5') | ~m1_subset_1(D_604, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.70/3.41  tff(c_4422, plain, (![A_591]: (k2_yellow_0('#skF_3', '#skF_6'(A_591))=A_591 | ~r2_hidden(A_591, '#skF_5'))), inference(resolution, [status(thm)], [c_4381, c_4412])).
% 9.70/3.41  tff(c_5146, plain, (![A_747, D_748, B_749]: (r1_orders_2(A_747, D_748, k2_yellow_0(A_747, B_749)) | ~r1_lattice3(A_747, B_749, D_748) | ~m1_subset_1(D_748, u1_struct_0(A_747)) | ~r2_yellow_0(A_747, B_749) | ~m1_subset_1(k2_yellow_0(A_747, B_749), u1_struct_0(A_747)) | ~l1_orders_2(A_747))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.70/3.41  tff(c_5148, plain, (![D_748, A_591]: (r1_orders_2('#skF_3', D_748, k2_yellow_0('#skF_3', '#skF_6'(A_591))) | ~r1_lattice3('#skF_3', '#skF_6'(A_591), D_748) | ~m1_subset_1(D_748, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_591)) | ~m1_subset_1(A_591, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(A_591, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4422, c_5146])).
% 9.70/3.41  tff(c_5671, plain, (![D_853, A_854]: (r1_orders_2('#skF_3', D_853, k2_yellow_0('#skF_3', '#skF_6'(A_854))) | ~r1_lattice3('#skF_3', '#skF_6'(A_854), D_853) | ~m1_subset_1(D_853, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_854)) | ~m1_subset_1(A_854, u1_struct_0('#skF_3')) | ~r2_hidden(A_854, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5148])).
% 9.70/3.41  tff(c_5682, plain, (![D_853, A_591]: (r1_orders_2('#skF_3', D_853, A_591) | ~r1_lattice3('#skF_3', '#skF_6'(A_591), D_853) | ~m1_subset_1(D_853, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_591)) | ~m1_subset_1(A_591, u1_struct_0('#skF_3')) | ~r2_hidden(A_591, '#skF_5') | ~r2_hidden(A_591, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4422, c_5671])).
% 9.70/3.41  tff(c_9260, plain, (![D_1099]: (r1_orders_2('#skF_3', '#skF_7', D_1099) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(D_1099)) | ~r2_hidden(D_1099, '#skF_5') | ~m1_subset_1(D_1099, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_9251, c_5682])).
% 9.70/3.41  tff(c_9971, plain, (![D_1114]: (r1_orders_2('#skF_3', '#skF_7', D_1114) | ~r2_yellow_0('#skF_3', '#skF_6'(D_1114)) | ~r2_hidden(D_1114, '#skF_5') | ~m1_subset_1(D_1114, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9260])).
% 9.70/3.41  tff(c_10072, plain, (![D_1118]: (r1_orders_2('#skF_3', '#skF_7', D_1118) | ~r2_hidden(D_1118, '#skF_5') | ~m1_subset_1(D_1118, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_9971])).
% 9.70/3.41  tff(c_10105, plain, (![A_1119]: (r1_orders_2('#skF_3', '#skF_7', A_1119) | ~r2_hidden(A_1119, '#skF_5'))), inference(resolution, [status(thm)], [c_4381, c_10072])).
% 9.70/3.41  tff(c_10156, plain, (![B_25]: (r1_lattice3('#skF_3', B_25, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_25, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_10105, c_22])).
% 9.70/3.41  tff(c_10203, plain, (![B_1120]: (r1_lattice3('#skF_3', B_1120, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1120, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_10156])).
% 9.70/3.41  tff(c_10218, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_10203])).
% 9.70/3.41  tff(c_10228, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_10218])).
% 9.70/3.41  tff(c_10230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4361, c_10228])).
% 9.70/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.70/3.41  
% 9.70/3.41  Inference rules
% 9.70/3.41  ----------------------
% 9.70/3.41  #Ref     : 0
% 9.70/3.41  #Sup     : 2245
% 9.70/3.41  #Fact    : 0
% 9.70/3.41  #Define  : 0
% 9.70/3.41  #Split   : 23
% 9.70/3.41  #Chain   : 0
% 9.70/3.41  #Close   : 0
% 9.70/3.41  
% 9.70/3.41  Ordering : KBO
% 9.70/3.41  
% 9.70/3.41  Simplification rules
% 9.70/3.41  ----------------------
% 9.70/3.41  #Subsume      : 688
% 9.70/3.41  #Demod        : 1393
% 9.70/3.41  #Tautology    : 134
% 9.70/3.41  #SimpNegUnit  : 124
% 9.70/3.41  #BackRed      : 0
% 9.70/3.41  
% 9.70/3.41  #Partial instantiations: 0
% 9.70/3.41  #Strategies tried      : 1
% 9.70/3.41  
% 9.70/3.41  Timing (in seconds)
% 9.70/3.41  ----------------------
% 9.70/3.42  Preprocessing        : 0.36
% 9.70/3.42  Parsing              : 0.19
% 9.70/3.42  CNF conversion       : 0.03
% 9.70/3.42  Main loop            : 2.29
% 9.70/3.42  Inferencing          : 0.75
% 9.70/3.42  Reduction            : 0.67
% 9.70/3.42  Demodulation         : 0.44
% 9.70/3.42  BG Simplification    : 0.07
% 9.70/3.42  Subsumption          : 0.63
% 9.70/3.42  Abstraction          : 0.10
% 9.70/3.42  MUC search           : 0.00
% 9.70/3.42  Cooper               : 0.00
% 9.70/3.42  Total                : 2.70
% 9.70/3.42  Index Insertion      : 0.00
% 9.70/3.42  Index Deletion       : 0.00
% 9.70/3.42  Index Matching       : 0.00
% 9.70/3.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
