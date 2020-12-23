%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1524+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:59 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 804 expanded)
%              Number of leaves         :   28 ( 275 expanded)
%              Depth                    :   24
%              Number of atoms          :  588 (3141 expanded)
%              Number of equality atoms :   79 ( 832 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C,D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( D = E
                       => ( ( r2_lattice3(A,C,D)
                           => r2_lattice3(B,C,E) )
                          & ( r1_lattice3(A,C,D)
                           => r1_lattice3(B,C,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

tff(f_38,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( C = E
                                & D = F )
                             => ( ( r1_orders_2(A,C,D)
                                 => r1_orders_2(B,E,F) )
                                & ( r2_orders_2(A,C,D)
                                 => r2_orders_2(B,E,F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(c_28,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_42,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_49,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_3529,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_47,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_44,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_6')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_55,plain,(
    ~ r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_61,plain,(
    ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_46,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_6')
    | r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8,plain,(
    ! [A_1,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_1,B_8,C_9),u1_struct_0(A_1))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_18,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_orders_2(A_25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_25),u1_struct_0(A_25))))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_67,plain,(
    ! [D_110,B_111,C_112,A_113] :
      ( D_110 = B_111
      | g1_orders_2(C_112,D_110) != g1_orders_2(A_113,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    ! [B_127,A_128] :
      ( u1_orders_2('#skF_3') = B_127
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_128,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_88,plain,(
    ! [A_25] :
      ( u1_orders_2(A_25) = u1_orders_2('#skF_3')
      | g1_orders_2(u1_struct_0(A_25),u1_orders_2(A_25)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_91,plain,
    ( u1_orders_2('#skF_3') = u1_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_93,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_108,plain,
    ( m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_18])).

tff(c_112,plain,(
    m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_108])).

tff(c_104,plain,(
    g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_4')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_34])).

tff(c_22,plain,(
    ! [C_30,A_26,D_31,B_27] :
      ( C_30 = A_26
      | g1_orders_2(C_30,D_31) != g1_orders_2(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_118,plain,(
    ! [C_30,D_31] :
      ( u1_struct_0('#skF_3') = C_30
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31)
      | ~ m1_subset_1(u1_orders_2('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_22])).

tff(c_126,plain,(
    ! [C_30,D_31] :
      ( u1_struct_0('#skF_3') = C_30
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_118])).

tff(c_132,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_126])).

tff(c_6,plain,(
    ! [A_1,B_8,C_9] :
      ( r2_hidden('#skF_1'(A_1,B_8,C_9),B_8)
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_198,plain,(
    ! [A_153,C_154,D_155,B_156] :
      ( r1_orders_2(A_153,C_154,D_155)
      | ~ r2_hidden(D_155,B_156)
      | ~ m1_subset_1(D_155,u1_struct_0(A_153))
      | ~ r1_lattice3(A_153,B_156,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_261,plain,(
    ! [B_183,C_185,A_187,C_184,A_186] :
      ( r1_orders_2(A_187,C_185,'#skF_1'(A_186,B_183,C_184))
      | ~ m1_subset_1('#skF_1'(A_186,B_183,C_184),u1_struct_0(A_187))
      | ~ r1_lattice3(A_187,B_183,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | r1_lattice3(A_186,B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186) ) ),
    inference(resolution,[status(thm)],[c_6,c_198])).

tff(c_267,plain,(
    ! [C_185,A_186,B_183,C_184] :
      ( r1_orders_2('#skF_3',C_185,'#skF_1'(A_186,B_183,C_184))
      | ~ m1_subset_1('#skF_1'(A_186,B_183,C_184),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_183,C_185)
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r1_lattice3(A_186,B_183,C_184)
      | ~ m1_subset_1(C_184,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_261])).

tff(c_293,plain,(
    ! [C_195,A_196,B_197,C_198] :
      ( r1_orders_2('#skF_3',C_195,'#skF_1'(A_196,B_197,C_198))
      | ~ m1_subset_1('#skF_1'(A_196,B_197,C_198),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_197,C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_4'))
      | r1_lattice3(A_196,B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ l1_orders_2(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_132,c_267])).

tff(c_298,plain,(
    ! [C_195,B_8,C_9] :
      ( r1_orders_2('#skF_3',C_195,'#skF_1'('#skF_4',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_293])).

tff(c_352,plain,(
    ! [C_206,B_207,C_208] :
      ( r1_orders_2('#skF_3',C_206,'#skF_1'('#skF_4',B_207,C_208))
      | ~ r1_lattice3('#skF_3',B_207,C_206)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_207,C_208)
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_298])).

tff(c_26,plain,(
    ! [B_64,E_92,F_94,A_32] :
      ( r1_orders_2(B_64,E_92,F_94)
      | ~ r1_orders_2(A_32,E_92,F_94)
      | ~ m1_subset_1(F_94,u1_struct_0(B_64))
      | ~ m1_subset_1(E_92,u1_struct_0(B_64))
      | ~ m1_subset_1(F_94,u1_struct_0(A_32))
      | ~ m1_subset_1(E_92,u1_struct_0(A_32))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0(A_32),u1_orders_2(A_32))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_354,plain,(
    ! [B_64,C_206,B_207,C_208] :
      ( r1_orders_2(B_64,C_206,'#skF_1'('#skF_4',B_207,C_208))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_207,C_208),u1_struct_0(B_64))
      | ~ m1_subset_1(C_206,u1_struct_0(B_64))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_207,C_208),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_207,C_206)
      | ~ m1_subset_1(C_206,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_207,C_208)
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_352,c_26])).

tff(c_910,plain,(
    ! [B_450,C_451,B_452,C_453] :
      ( r1_orders_2(B_450,C_451,'#skF_1'('#skF_4',B_452,C_453))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_452,C_453),u1_struct_0(B_450))
      | ~ m1_subset_1(C_451,u1_struct_0(B_450))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_452,C_453),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_450),u1_orders_2(B_450)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_450)
      | ~ r1_lattice3('#skF_3',B_452,C_451)
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_452,C_453)
      | ~ m1_subset_1(C_453,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_132,c_93,c_132,c_132,c_354])).

tff(c_913,plain,(
    ! [C_451,B_8,C_9] :
      ( r1_orders_2('#skF_4',C_451,'#skF_1'('#skF_4',B_8,C_9))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_8,C_9),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_8,C_451)
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_910])).

tff(c_921,plain,(
    ! [C_454,B_455,C_456] :
      ( r1_orders_2('#skF_4',C_454,'#skF_1'('#skF_4',B_455,C_456))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_455,C_456),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_455,C_454)
      | ~ m1_subset_1(C_454,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_455,C_456)
      | ~ m1_subset_1(C_456,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_913])).

tff(c_924,plain,(
    ! [C_454,B_8,C_9] :
      ( r1_orders_2('#skF_4',C_454,'#skF_1'('#skF_4',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,C_454)
      | ~ m1_subset_1(C_454,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_921])).

tff(c_928,plain,(
    ! [C_457,B_458,C_459] :
      ( r1_orders_2('#skF_4',C_457,'#skF_1'('#skF_4',B_458,C_459))
      | ~ r1_lattice3('#skF_3',B_458,C_457)
      | ~ m1_subset_1(C_457,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_458,C_459)
      | ~ m1_subset_1(C_459,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_924])).

tff(c_4,plain,(
    ! [A_1,C_9,B_8] :
      ( ~ r1_orders_2(A_1,C_9,'#skF_1'(A_1,B_8,C_9))
      | r1_lattice3(A_1,B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_934,plain,(
    ! [B_458,C_459] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_458,C_459)
      | r1_lattice3('#skF_4',B_458,C_459)
      | ~ m1_subset_1(C_459,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_928,c_4])).

tff(c_948,plain,(
    ! [B_460,C_461] :
      ( ~ r1_lattice3('#skF_3',B_460,C_461)
      | r1_lattice3('#skF_4',B_460,C_461)
      | ~ m1_subset_1(C_461,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_934])).

tff(c_960,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_948])).

tff(c_970,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_960])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_970])).

tff(c_973,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_16,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_989,plain,(
    ! [C_467,A_468,D_469,B_470] :
      ( C_467 = A_468
      | g1_orders_2(C_467,D_469) != g1_orders_2(A_468,B_470)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k2_zfmisc_1(A_468,A_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_999,plain,(
    ! [A_486,B_487] :
      ( u1_struct_0('#skF_3') = A_486
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_486,B_487)
      | ~ m1_subset_1(B_487,k1_zfmisc_1(k2_zfmisc_1(A_486,A_486))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_989])).

tff(c_1003,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_25),u1_orders_2(A_25)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_999])).

tff(c_1006,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1003])).

tff(c_1008,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1006])).

tff(c_1031,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_18])).

tff(c_1042,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1008,c_1031])).

tff(c_1019,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_34])).

tff(c_20,plain,(
    ! [D_31,B_27,C_30,A_26] :
      ( D_31 = B_27
      | g1_orders_2(C_30,D_31) != g1_orders_2(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1055,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_20])).

tff(c_1061,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_1055])).

tff(c_1075,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1061])).

tff(c_14,plain,(
    ! [A_13,B_20,C_21] :
      ( r2_hidden('#skF_2'(A_13,B_20,C_21),B_20)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1115,plain,(
    ! [A_506,D_507,C_508,B_509] :
      ( r1_orders_2(A_506,D_507,C_508)
      | ~ r2_hidden(D_507,B_509)
      | ~ m1_subset_1(D_507,u1_struct_0(A_506))
      | ~ r2_lattice3(A_506,B_509,C_508)
      | ~ m1_subset_1(C_508,u1_struct_0(A_506))
      | ~ l1_orders_2(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1355,plain,(
    ! [C_584,A_588,C_587,A_585,B_586] :
      ( r1_orders_2(A_585,'#skF_2'(A_588,B_586,C_584),C_587)
      | ~ m1_subset_1('#skF_2'(A_588,B_586,C_584),u1_struct_0(A_585))
      | ~ r2_lattice3(A_585,B_586,C_587)
      | ~ m1_subset_1(C_587,u1_struct_0(A_585))
      | ~ l1_orders_2(A_585)
      | r2_lattice3(A_588,B_586,C_584)
      | ~ m1_subset_1(C_584,u1_struct_0(A_588))
      | ~ l1_orders_2(A_588) ) ),
    inference(resolution,[status(thm)],[c_14,c_1115])).

tff(c_1359,plain,(
    ! [A_588,B_586,C_584,C_587] :
      ( r1_orders_2('#skF_3','#skF_2'(A_588,B_586,C_584),C_587)
      | ~ m1_subset_1('#skF_2'(A_588,B_586,C_584),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_586,C_587)
      | ~ m1_subset_1(C_587,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r2_lattice3(A_588,B_586,C_584)
      | ~ m1_subset_1(C_584,u1_struct_0(A_588))
      | ~ l1_orders_2(A_588) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1355])).

tff(c_1395,plain,(
    ! [A_596,B_597,C_598,C_599] :
      ( r1_orders_2('#skF_3','#skF_2'(A_596,B_597,C_598),C_599)
      | ~ m1_subset_1('#skF_2'(A_596,B_597,C_598),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_597,C_599)
      | ~ m1_subset_1(C_599,u1_struct_0('#skF_4'))
      | r2_lattice3(A_596,B_597,C_598)
      | ~ m1_subset_1(C_598,u1_struct_0(A_596))
      | ~ l1_orders_2(A_596) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1008,c_1359])).

tff(c_1400,plain,(
    ! [B_20,C_21,C_599] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_20,C_21),C_599)
      | ~ r2_lattice3('#skF_3',B_20,C_599)
      | ~ m1_subset_1(C_599,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1395])).

tff(c_1428,plain,(
    ! [B_607,C_608,C_609] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_607,C_608),C_609)
      | ~ r2_lattice3('#skF_3',B_607,C_609)
      | ~ m1_subset_1(C_609,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_607,C_608)
      | ~ m1_subset_1(C_608,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1400])).

tff(c_1430,plain,(
    ! [B_64,B_607,C_608,C_609] :
      ( r1_orders_2(B_64,'#skF_2'('#skF_4',B_607,C_608),C_609)
      | ~ m1_subset_1(C_609,u1_struct_0(B_64))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_607,C_608),u1_struct_0(B_64))
      | ~ m1_subset_1(C_609,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_607,C_608),u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_lattice3('#skF_3',B_607,C_609)
      | ~ m1_subset_1(C_609,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_607,C_608)
      | ~ m1_subset_1(C_608,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1428,c_26])).

tff(c_2148,plain,(
    ! [B_894,B_895,C_896,C_897] :
      ( r1_orders_2(B_894,'#skF_2'('#skF_4',B_895,C_896),C_897)
      | ~ m1_subset_1(C_897,u1_struct_0(B_894))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_895,C_896),u1_struct_0(B_894))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_895,C_896),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_894),u1_orders_2(B_894)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_894)
      | ~ r2_lattice3('#skF_3',B_895,C_897)
      | ~ m1_subset_1(C_897,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_895,C_896)
      | ~ m1_subset_1(C_896,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1075,c_1008,c_1008,c_1008,c_1430])).

tff(c_2153,plain,(
    ! [B_20,C_21,C_897] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_897)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_20,C_21),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_20,C_897)
      | ~ m1_subset_1(C_897,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_2148])).

tff(c_2159,plain,(
    ! [B_898,C_899,C_900] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_898,C_899),C_900)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_898,C_899),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_898,C_900)
      | ~ m1_subset_1(C_900,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_898,C_899)
      | ~ m1_subset_1(C_899,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2153])).

tff(c_2162,plain,(
    ! [B_20,C_21,C_900] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_900)
      | ~ r2_lattice3('#skF_3',B_20,C_900)
      | ~ m1_subset_1(C_900,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_2159])).

tff(c_2166,plain,(
    ! [B_901,C_902,C_903] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_901,C_902),C_903)
      | ~ r2_lattice3('#skF_3',B_901,C_903)
      | ~ m1_subset_1(C_903,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_901,C_902)
      | ~ m1_subset_1(C_902,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2162])).

tff(c_12,plain,(
    ! [A_13,B_20,C_21] :
      ( ~ r1_orders_2(A_13,'#skF_2'(A_13,B_20,C_21),C_21)
      | r2_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2176,plain,(
    ! [B_901,C_903] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_3',B_901,C_903)
      | r2_lattice3('#skF_4',B_901,C_903)
      | ~ m1_subset_1(C_903,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2166,c_12])).

tff(c_2186,plain,(
    ! [B_904,C_905] :
      ( ~ r2_lattice3('#skF_3',B_904,C_905)
      | r2_lattice3('#skF_4',B_904,C_905)
      | ~ m1_subset_1(C_905,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2176])).

tff(c_2198,plain,
    ( r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_973,c_2186])).

tff(c_2208,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_2198])).

tff(c_2210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_2208])).

tff(c_2211,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2223,plain,(
    ! [C_907,A_908,D_909,B_910] :
      ( C_907 = A_908
      | g1_orders_2(C_907,D_909) != g1_orders_2(A_908,B_910)
      | ~ m1_subset_1(B_910,k1_zfmisc_1(k2_zfmisc_1(A_908,A_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2240,plain,(
    ! [A_924,B_925] :
      ( u1_struct_0('#skF_3') = A_924
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_924,B_925)
      | ~ m1_subset_1(B_925,k1_zfmisc_1(k2_zfmisc_1(A_924,A_924))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2223])).

tff(c_2244,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_25),u1_orders_2(A_25)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_2240])).

tff(c_2247,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2244])).

tff(c_2249,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2247])).

tff(c_2266,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_18])).

tff(c_2273,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2249,c_2266])).

tff(c_2260,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2249,c_34])).

tff(c_2282,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2260,c_20])).

tff(c_2290,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_2282])).

tff(c_2297,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2290])).

tff(c_2347,plain,(
    ! [A_946,D_947,C_948,B_949] :
      ( r1_orders_2(A_946,D_947,C_948)
      | ~ r2_hidden(D_947,B_949)
      | ~ m1_subset_1(D_947,u1_struct_0(A_946))
      | ~ r2_lattice3(A_946,B_949,C_948)
      | ~ m1_subset_1(C_948,u1_struct_0(A_946))
      | ~ l1_orders_2(A_946) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2521,plain,(
    ! [A_1008,C_1007,A_1010,C_1006,B_1009] :
      ( r1_orders_2(A_1008,'#skF_2'(A_1010,B_1009,C_1006),C_1007)
      | ~ m1_subset_1('#skF_2'(A_1010,B_1009,C_1006),u1_struct_0(A_1008))
      | ~ r2_lattice3(A_1008,B_1009,C_1007)
      | ~ m1_subset_1(C_1007,u1_struct_0(A_1008))
      | ~ l1_orders_2(A_1008)
      | r2_lattice3(A_1010,B_1009,C_1006)
      | ~ m1_subset_1(C_1006,u1_struct_0(A_1010))
      | ~ l1_orders_2(A_1010) ) ),
    inference(resolution,[status(thm)],[c_14,c_2347])).

tff(c_2527,plain,(
    ! [A_1010,B_1009,C_1006,C_1007] :
      ( r1_orders_2('#skF_3','#skF_2'(A_1010,B_1009,C_1006),C_1007)
      | ~ m1_subset_1('#skF_2'(A_1010,B_1009,C_1006),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1009,C_1007)
      | ~ m1_subset_1(C_1007,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r2_lattice3(A_1010,B_1009,C_1006)
      | ~ m1_subset_1(C_1006,u1_struct_0(A_1010))
      | ~ l1_orders_2(A_1010) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_2521])).

tff(c_2547,plain,(
    ! [A_1014,B_1015,C_1016,C_1017] :
      ( r1_orders_2('#skF_3','#skF_2'(A_1014,B_1015,C_1016),C_1017)
      | ~ m1_subset_1('#skF_2'(A_1014,B_1015,C_1016),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1015,C_1017)
      | ~ m1_subset_1(C_1017,u1_struct_0('#skF_4'))
      | r2_lattice3(A_1014,B_1015,C_1016)
      | ~ m1_subset_1(C_1016,u1_struct_0(A_1014))
      | ~ l1_orders_2(A_1014) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2249,c_2527])).

tff(c_2552,plain,(
    ! [B_20,C_21,C_1017] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_20,C_21),C_1017)
      | ~ r2_lattice3('#skF_3',B_20,C_1017)
      | ~ m1_subset_1(C_1017,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_2547])).

tff(c_2579,plain,(
    ! [B_1021,C_1022,C_1023] :
      ( r1_orders_2('#skF_3','#skF_2'('#skF_4',B_1021,C_1022),C_1023)
      | ~ r2_lattice3('#skF_3',B_1021,C_1023)
      | ~ m1_subset_1(C_1023,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_1021,C_1022)
      | ~ m1_subset_1(C_1022,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2552])).

tff(c_2581,plain,(
    ! [B_64,B_1021,C_1022,C_1023] :
      ( r1_orders_2(B_64,'#skF_2'('#skF_4',B_1021,C_1022),C_1023)
      | ~ m1_subset_1(C_1023,u1_struct_0(B_64))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1021,C_1022),u1_struct_0(B_64))
      | ~ m1_subset_1(C_1023,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1021,C_1022),u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_lattice3('#skF_3',B_1021,C_1023)
      | ~ m1_subset_1(C_1023,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_1021,C_1022)
      | ~ m1_subset_1(C_1022,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2579,c_26])).

tff(c_3464,plain,(
    ! [B_1379,B_1380,C_1381,C_1382] :
      ( r1_orders_2(B_1379,'#skF_2'('#skF_4',B_1380,C_1381),C_1382)
      | ~ m1_subset_1(C_1382,u1_struct_0(B_1379))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1380,C_1381),u1_struct_0(B_1379))
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1380,C_1381),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_1379),u1_orders_2(B_1379)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_1379)
      | ~ r2_lattice3('#skF_3',B_1380,C_1382)
      | ~ m1_subset_1(C_1382,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_1380,C_1381)
      | ~ m1_subset_1(C_1381,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2297,c_2249,c_2249,c_2249,c_2581])).

tff(c_3467,plain,(
    ! [B_20,C_21,C_1382] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_1382)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_20,C_21),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_20,C_1382)
      | ~ m1_subset_1(C_1382,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3464])).

tff(c_3475,plain,(
    ! [B_1383,C_1384,C_1385] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_1383,C_1384),C_1385)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_1383,C_1384),u1_struct_0('#skF_4'))
      | ~ r2_lattice3('#skF_3',B_1383,C_1385)
      | ~ m1_subset_1(C_1385,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_1383,C_1384)
      | ~ m1_subset_1(C_1384,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3467])).

tff(c_3478,plain,(
    ! [B_20,C_21,C_1385] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_20,C_21),C_1385)
      | ~ r2_lattice3('#skF_3',B_20,C_1385)
      | ~ m1_subset_1(C_1385,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3475])).

tff(c_3482,plain,(
    ! [B_1386,C_1387,C_1388] :
      ( r1_orders_2('#skF_4','#skF_2'('#skF_4',B_1386,C_1387),C_1388)
      | ~ r2_lattice3('#skF_3',B_1386,C_1388)
      | ~ m1_subset_1(C_1388,u1_struct_0('#skF_4'))
      | r2_lattice3('#skF_4',B_1386,C_1387)
      | ~ m1_subset_1(C_1387,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3478])).

tff(c_3492,plain,(
    ! [B_1386,C_1388] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r2_lattice3('#skF_3',B_1386,C_1388)
      | r2_lattice3('#skF_4',B_1386,C_1388)
      | ~ m1_subset_1(C_1388,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3482,c_12])).

tff(c_3502,plain,(
    ! [B_1389,C_1390] :
      ( ~ r2_lattice3('#skF_3',B_1389,C_1390)
      | r2_lattice3('#skF_4',B_1389,C_1390)
      | ~ m1_subset_1(C_1390,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3492])).

tff(c_3514,plain,
    ( r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2211,c_3502])).

tff(c_3524,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_3514])).

tff(c_3526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_3524])).

tff(c_3527,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3542,plain,(
    ! [C_1392,A_1393,D_1394,B_1395] :
      ( C_1392 = A_1393
      | g1_orders_2(C_1392,D_1394) != g1_orders_2(A_1393,B_1395)
      | ~ m1_subset_1(B_1395,k1_zfmisc_1(k2_zfmisc_1(A_1393,A_1393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3562,plain,(
    ! [A_1418,B_1419] :
      ( u1_struct_0('#skF_3') = A_1418
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_1418,B_1419)
      | ~ m1_subset_1(B_1419,k1_zfmisc_1(k2_zfmisc_1(A_1418,A_1418))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3542])).

tff(c_3566,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = u1_struct_0('#skF_3')
      | g1_orders_2(u1_struct_0(A_25),u1_orders_2(A_25)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_18,c_3562])).

tff(c_3569,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3566])).

tff(c_3571,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3569])).

tff(c_3599,plain,
    ( m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ l1_orders_2('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_18])).

tff(c_3610,plain,(
    m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3571,c_3599])).

tff(c_3587,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_3')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3571,c_34])).

tff(c_3624,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31)
      | ~ m1_subset_1(u1_orders_2('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3587,c_20])).

tff(c_3632,plain,(
    ! [D_31,C_30] :
      ( u1_orders_2('#skF_3') = D_31
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_30,D_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_3624])).

tff(c_3638,plain,(
    u1_orders_2('#skF_3') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3632])).

tff(c_3680,plain,(
    ! [A_1437,C_1438,D_1439,B_1440] :
      ( r1_orders_2(A_1437,C_1438,D_1439)
      | ~ r2_hidden(D_1439,B_1440)
      | ~ m1_subset_1(D_1439,u1_struct_0(A_1437))
      | ~ r1_lattice3(A_1437,B_1440,C_1438)
      | ~ m1_subset_1(C_1438,u1_struct_0(A_1437))
      | ~ l1_orders_2(A_1437) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3812,plain,(
    ! [A_1489,C_1493,A_1492,C_1491,B_1490] :
      ( r1_orders_2(A_1489,C_1493,'#skF_1'(A_1492,B_1490,C_1491))
      | ~ m1_subset_1('#skF_1'(A_1492,B_1490,C_1491),u1_struct_0(A_1489))
      | ~ r1_lattice3(A_1489,B_1490,C_1493)
      | ~ m1_subset_1(C_1493,u1_struct_0(A_1489))
      | ~ l1_orders_2(A_1489)
      | r1_lattice3(A_1492,B_1490,C_1491)
      | ~ m1_subset_1(C_1491,u1_struct_0(A_1492))
      | ~ l1_orders_2(A_1492) ) ),
    inference(resolution,[status(thm)],[c_6,c_3680])).

tff(c_3816,plain,(
    ! [C_1493,A_1492,B_1490,C_1491] :
      ( r1_orders_2('#skF_3',C_1493,'#skF_1'(A_1492,B_1490,C_1491))
      | ~ m1_subset_1('#skF_1'(A_1492,B_1490,C_1491),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1490,C_1493)
      | ~ m1_subset_1(C_1493,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | r1_lattice3(A_1492,B_1490,C_1491)
      | ~ m1_subset_1(C_1491,u1_struct_0(A_1492))
      | ~ l1_orders_2(A_1492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_3812])).

tff(c_3844,plain,(
    ! [C_1501,A_1502,B_1503,C_1504] :
      ( r1_orders_2('#skF_3',C_1501,'#skF_1'(A_1502,B_1503,C_1504))
      | ~ m1_subset_1('#skF_1'(A_1502,B_1503,C_1504),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1503,C_1501)
      | ~ m1_subset_1(C_1501,u1_struct_0('#skF_4'))
      | r1_lattice3(A_1502,B_1503,C_1504)
      | ~ m1_subset_1(C_1504,u1_struct_0(A_1502))
      | ~ l1_orders_2(A_1502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3571,c_3816])).

tff(c_3849,plain,(
    ! [C_1501,B_8,C_9] :
      ( r1_orders_2('#skF_3',C_1501,'#skF_1'('#skF_4',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,C_1501)
      | ~ m1_subset_1(C_1501,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_3844])).

tff(c_3921,plain,(
    ! [C_1512,B_1513,C_1514] :
      ( r1_orders_2('#skF_3',C_1512,'#skF_1'('#skF_4',B_1513,C_1514))
      | ~ r1_lattice3('#skF_3',B_1513,C_1512)
      | ~ m1_subset_1(C_1512,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_1513,C_1514)
      | ~ m1_subset_1(C_1514,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3849])).

tff(c_3923,plain,(
    ! [B_64,C_1512,B_1513,C_1514] :
      ( r1_orders_2(B_64,C_1512,'#skF_1'('#skF_4',B_1513,C_1514))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1513,C_1514),u1_struct_0(B_64))
      | ~ m1_subset_1(C_1512,u1_struct_0(B_64))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1513,C_1514),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1512,u1_struct_0('#skF_3'))
      | g1_orders_2(u1_struct_0(B_64),u1_orders_2(B_64)) != g1_orders_2(u1_struct_0('#skF_3'),u1_orders_2('#skF_3'))
      | ~ l1_orders_2(B_64)
      | ~ l1_orders_2('#skF_3')
      | ~ r1_lattice3('#skF_3',B_1513,C_1512)
      | ~ m1_subset_1(C_1512,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_1513,C_1514)
      | ~ m1_subset_1(C_1514,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3921,c_26])).

tff(c_4592,plain,(
    ! [B_1802,C_1803,B_1804,C_1805] :
      ( r1_orders_2(B_1802,C_1803,'#skF_1'('#skF_4',B_1804,C_1805))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1804,C_1805),u1_struct_0(B_1802))
      | ~ m1_subset_1(C_1803,u1_struct_0(B_1802))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1804,C_1805),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_1802),u1_orders_2(B_1802)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_1802)
      | ~ r1_lattice3('#skF_3',B_1804,C_1803)
      | ~ m1_subset_1(C_1803,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_1804,C_1805)
      | ~ m1_subset_1(C_1805,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3638,c_3571,c_3571,c_3571,c_3923])).

tff(c_4597,plain,(
    ! [C_1803,B_8,C_9] :
      ( r1_orders_2('#skF_4',C_1803,'#skF_1'('#skF_4',B_8,C_9))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_8,C_9),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_8,C_1803)
      | ~ m1_subset_1(C_1803,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_4592])).

tff(c_4603,plain,(
    ! [C_1806,B_1807,C_1808] :
      ( r1_orders_2('#skF_4',C_1806,'#skF_1'('#skF_4',B_1807,C_1808))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1807,C_1808),u1_struct_0('#skF_4'))
      | ~ r1_lattice3('#skF_3',B_1807,C_1806)
      | ~ m1_subset_1(C_1806,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_1807,C_1808)
      | ~ m1_subset_1(C_1808,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4597])).

tff(c_4606,plain,(
    ! [C_1806,B_8,C_9] :
      ( r1_orders_2('#skF_4',C_1806,'#skF_1'('#skF_4',B_8,C_9))
      | ~ r1_lattice3('#skF_3',B_8,C_1806)
      | ~ m1_subset_1(C_1806,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_8,C_9)
      | ~ m1_subset_1(C_9,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_4603])).

tff(c_4610,plain,(
    ! [C_1809,B_1810,C_1811] :
      ( r1_orders_2('#skF_4',C_1809,'#skF_1'('#skF_4',B_1810,C_1811))
      | ~ r1_lattice3('#skF_3',B_1810,C_1809)
      | ~ m1_subset_1(C_1809,u1_struct_0('#skF_4'))
      | r1_lattice3('#skF_4',B_1810,C_1811)
      | ~ m1_subset_1(C_1811,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4606])).

tff(c_4620,plain,(
    ! [B_1810,C_1811] :
      ( ~ l1_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_3',B_1810,C_1811)
      | r1_lattice3('#skF_4',B_1810,C_1811)
      | ~ m1_subset_1(C_1811,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4610,c_4])).

tff(c_4630,plain,(
    ! [B_1812,C_1813] :
      ( ~ r1_lattice3('#skF_3',B_1812,C_1813)
      | r1_lattice3('#skF_4',B_1812,C_1813)
      | ~ m1_subset_1(C_1813,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4620])).

tff(c_4632,plain,
    ( r1_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3527,c_4630])).

tff(c_4635,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_4632])).

tff(c_4637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3529,c_4635])).

tff(c_4639,plain,(
    r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_3528,plain,(
    r2_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_40,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,
    ( ~ r2_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ r1_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_40])).

tff(c_4642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4639,c_3528,c_50])).

%------------------------------------------------------------------------------
