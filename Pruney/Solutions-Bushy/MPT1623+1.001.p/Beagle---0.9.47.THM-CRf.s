%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:08 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  109 (1459 expanded)
%              Number of leaves         :   26 ( 504 expanded)
%              Depth                    :   25
%              Number of atoms          :  368 (5767 expanded)
%              Number of equality atoms :   33 (1517 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v1_waybel_0 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( ( C = D
                          & v1_waybel_0(C,A) )
                       => v1_waybel_0(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_0)).

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

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(C,B)
                        & r2_hidden(D,B)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ~ ( r2_hidden(E,B)
                                & r1_orders_2(A,C,E)
                                & r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

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

tff(c_34,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ~ v1_waybel_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    ~ v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [A_57] :
      ( m1_subset_1(u1_orders_2(A_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57),u1_struct_0(A_57))))
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_60,plain,(
    ! [C_139,A_140,D_141,B_142] :
      ( C_139 = A_140
      | g1_orders_2(C_139,D_141) != g1_orders_2(A_140,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_140,A_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    ! [A_155,B_156] :
      ( u1_struct_0('#skF_5') = A_155
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_155,A_155))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_60])).

tff(c_104,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = u1_struct_0('#skF_5')
      | g1_orders_2(u1_struct_0(A_57),u1_orders_2(A_57)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_107,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_104])).

tff(c_109,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_107])).

tff(c_10,plain,(
    ! [A_1,B_31] :
      ( m1_subset_1('#skF_2'(A_1,B_31),u1_struct_0(A_1))
      | v1_waybel_0(B_31,A_1)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_131,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_2'('#skF_5',B_31),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_31,'#skF_5')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_10])).

tff(c_148,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_2'('#skF_5',B_31),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_31,'#skF_5')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_109,c_131])).

tff(c_32,plain,(
    v1_waybel_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_1,B_31] :
      ( m1_subset_1('#skF_3'(A_1,B_31),u1_struct_0(A_1))
      | v1_waybel_0(B_31,A_1)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_3'('#skF_5',B_31),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_31,'#skF_5')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_150,plain,(
    ! [B_31] :
      ( m1_subset_1('#skF_3'('#skF_5',B_31),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_31,'#skF_5')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_109,c_134])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_45,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_74,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_3'(A_147,B_148),B_148)
      | v1_waybel_0(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_orders_2(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_waybel_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_45,c_74])).

tff(c_81,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_76])).

tff(c_82,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_81])).

tff(c_86,plain,(
    ! [A_149,B_150] :
      ( r2_hidden('#skF_2'(A_149,B_150),B_150)
      | v1_waybel_0(B_150,A_149)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_orders_2(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v1_waybel_0('#skF_6','#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_45,c_86])).

tff(c_93,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_88])).

tff(c_94,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_93])).

tff(c_230,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( r2_hidden('#skF_1'(A_172,B_173,C_174,D_175),B_173)
      | ~ r2_hidden(D_175,B_173)
      | ~ r2_hidden(C_174,B_173)
      | ~ m1_subset_1(D_175,u1_struct_0(A_172))
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ v1_waybel_0(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_234,plain,(
    ! [C_174,D_175] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_6',C_174,D_175),'#skF_6')
      | ~ r2_hidden(D_175,'#skF_6')
      | ~ r2_hidden(C_174,'#skF_6')
      | ~ m1_subset_1(D_175,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_4'))
      | ~ v1_waybel_0('#skF_6','#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_230])).

tff(c_239,plain,(
    ! [C_174,D_175] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_6',C_174,D_175),'#skF_6')
      | ~ r2_hidden(D_175,'#skF_6')
      | ~ r2_hidden(C_174,'#skF_6')
      | ~ m1_subset_1(D_175,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_234])).

tff(c_18,plain,(
    ! [A_1,B_31,C_46,D_50] :
      ( m1_subset_1('#skF_1'(A_1,B_31,C_46,D_50),u1_struct_0(A_1))
      | ~ r2_hidden(D_50,B_31)
      | ~ r2_hidden(C_46,B_31)
      | ~ m1_subset_1(D_50,u1_struct_0(A_1))
      | ~ m1_subset_1(C_46,u1_struct_0(A_1))
      | ~ v1_waybel_0(B_31,A_1)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_141,plain,
    ( m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_20])).

tff(c_156,plain,(
    m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_109,c_141])).

tff(c_125,plain,(
    g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_5')) = g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_40])).

tff(c_22,plain,(
    ! [D_63,B_59,C_62,A_58] :
      ( D_63 = B_59
      | g1_orders_2(C_62,D_63) != g1_orders_2(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_zfmisc_1(A_58,A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    ! [D_63,C_62] :
      ( u1_orders_2('#skF_5') = D_63
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_62,D_63)
      | ~ m1_subset_1(u1_orders_2('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_22])).

tff(c_178,plain,(
    ! [D_63,C_62] :
      ( u1_orders_2('#skF_5') = D_63
      | g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4')) != g1_orders_2(C_62,D_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_170])).

tff(c_184,plain,(
    u1_orders_2('#skF_5') = u1_orders_2('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_178])).

tff(c_270,plain,(
    ! [A_191,D_192,B_193,C_194] :
      ( r1_orders_2(A_191,D_192,'#skF_1'(A_191,B_193,C_194,D_192))
      | ~ r2_hidden(D_192,B_193)
      | ~ r2_hidden(C_194,B_193)
      | ~ m1_subset_1(D_192,u1_struct_0(A_191))
      | ~ m1_subset_1(C_194,u1_struct_0(A_191))
      | ~ v1_waybel_0(B_193,A_191)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_orders_2(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_274,plain,(
    ! [D_192,C_194] :
      ( r1_orders_2('#skF_4',D_192,'#skF_1'('#skF_4','#skF_6',C_194,D_192))
      | ~ r2_hidden(D_192,'#skF_6')
      | ~ r2_hidden(C_194,'#skF_6')
      | ~ m1_subset_1(D_192,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_4'))
      | ~ v1_waybel_0('#skF_6','#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_270])).

tff(c_279,plain,(
    ! [D_192,C_194] :
      ( r1_orders_2('#skF_4',D_192,'#skF_1'('#skF_4','#skF_6',C_194,D_192))
      | ~ r2_hidden(D_192,'#skF_6')
      | ~ r2_hidden(C_194,'#skF_6')
      | ~ m1_subset_1(D_192,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_274])).

tff(c_304,plain,(
    ! [B_209,E_210,F_211,A_212] :
      ( r1_orders_2(B_209,E_210,F_211)
      | ~ r1_orders_2(A_212,E_210,F_211)
      | ~ m1_subset_1(F_211,u1_struct_0(B_209))
      | ~ m1_subset_1(E_210,u1_struct_0(B_209))
      | ~ m1_subset_1(F_211,u1_struct_0(A_212))
      | ~ m1_subset_1(E_210,u1_struct_0(A_212))
      | g1_orders_2(u1_struct_0(B_209),u1_orders_2(B_209)) != g1_orders_2(u1_struct_0(A_212),u1_orders_2(A_212))
      | ~ l1_orders_2(B_209)
      | ~ l1_orders_2(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_306,plain,(
    ! [B_209,D_192,C_194] :
      ( r1_orders_2(B_209,D_192,'#skF_1'('#skF_4','#skF_6',C_194,D_192))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_194,D_192),u1_struct_0(B_209))
      | ~ m1_subset_1(D_192,u1_struct_0(B_209))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_194,D_192),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_209),u1_orders_2(B_209)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_209)
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(D_192,'#skF_6')
      | ~ r2_hidden(C_194,'#skF_6')
      | ~ m1_subset_1(D_192,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_194,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_279,c_304])).

tff(c_323,plain,(
    ! [B_218,D_219,C_220] :
      ( r1_orders_2(B_218,D_219,'#skF_1'('#skF_4','#skF_6',C_220,D_219))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_220,D_219),u1_struct_0(B_218))
      | ~ m1_subset_1(D_219,u1_struct_0(B_218))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_220,D_219),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_218),u1_orders_2(B_218)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_218)
      | ~ r2_hidden(D_219,'#skF_6')
      | ~ r2_hidden(C_220,'#skF_6')
      | ~ m1_subset_1(D_219,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_306])).

tff(c_328,plain,(
    ! [D_219,C_220] :
      ( r1_orders_2('#skF_5',D_219,'#skF_1'('#skF_4','#skF_6',C_220,D_219))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_220,D_219),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_219,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_220,D_219),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden(D_219,'#skF_6')
      | ~ r2_hidden(C_220,'#skF_6')
      | ~ m1_subset_1(D_219,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_323])).

tff(c_345,plain,(
    ! [D_224,C_225] :
      ( r1_orders_2('#skF_5',D_224,'#skF_1'('#skF_4','#skF_6',C_225,D_224))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_225,D_224),u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_224,'#skF_6')
      | ~ r2_hidden(C_225,'#skF_6')
      | ~ m1_subset_1(D_224,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_225,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_184,c_109,c_109,c_328])).

tff(c_348,plain,(
    ! [D_50,C_46] :
      ( r1_orders_2('#skF_5',D_50,'#skF_1'('#skF_4','#skF_6',C_46,D_50))
      | ~ r2_hidden(D_50,'#skF_6')
      | ~ r2_hidden(C_46,'#skF_6')
      | ~ m1_subset_1(D_50,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_4'))
      | ~ v1_waybel_0('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_351,plain,(
    ! [D_50,C_46] :
      ( r1_orders_2('#skF_5',D_50,'#skF_1'('#skF_4','#skF_6',C_46,D_50))
      | ~ r2_hidden(D_50,'#skF_6')
      | ~ r2_hidden(C_46,'#skF_6')
      | ~ m1_subset_1(D_50,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_32,c_348])).

tff(c_249,plain,(
    ! [A_182,C_183,B_184,D_185] :
      ( r1_orders_2(A_182,C_183,'#skF_1'(A_182,B_184,C_183,D_185))
      | ~ r2_hidden(D_185,B_184)
      | ~ r2_hidden(C_183,B_184)
      | ~ m1_subset_1(D_185,u1_struct_0(A_182))
      | ~ m1_subset_1(C_183,u1_struct_0(A_182))
      | ~ v1_waybel_0(B_184,A_182)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_253,plain,(
    ! [C_183,D_185] :
      ( r1_orders_2('#skF_4',C_183,'#skF_1'('#skF_4','#skF_6',C_183,D_185))
      | ~ r2_hidden(D_185,'#skF_6')
      | ~ r2_hidden(C_183,'#skF_6')
      | ~ m1_subset_1(D_185,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_4'))
      | ~ v1_waybel_0('#skF_6','#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_249])).

tff(c_258,plain,(
    ! [C_183,D_185] :
      ( r1_orders_2('#skF_4',C_183,'#skF_1'('#skF_4','#skF_6',C_183,D_185))
      | ~ r2_hidden(D_185,'#skF_6')
      | ~ r2_hidden(C_183,'#skF_6')
      | ~ m1_subset_1(D_185,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_253])).

tff(c_308,plain,(
    ! [B_209,C_183,D_185] :
      ( r1_orders_2(B_209,C_183,'#skF_1'('#skF_4','#skF_6',C_183,D_185))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_183,D_185),u1_struct_0(B_209))
      | ~ m1_subset_1(C_183,u1_struct_0(B_209))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_183,D_185),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_209),u1_orders_2(B_209)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_209)
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(D_185,'#skF_6')
      | ~ r2_hidden(C_183,'#skF_6')
      | ~ m1_subset_1(D_185,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_258,c_304])).

tff(c_334,plain,(
    ! [B_221,C_222,D_223] :
      ( r1_orders_2(B_221,C_222,'#skF_1'('#skF_4','#skF_6',C_222,D_223))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_222,D_223),u1_struct_0(B_221))
      | ~ m1_subset_1(C_222,u1_struct_0(B_221))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_222,D_223),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0(B_221),u1_orders_2(B_221)) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2(B_221)
      | ~ r2_hidden(D_223,'#skF_6')
      | ~ r2_hidden(C_222,'#skF_6')
      | ~ m1_subset_1(D_223,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_222,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_308])).

tff(c_339,plain,(
    ! [C_222,D_223] :
      ( r1_orders_2('#skF_5',C_222,'#skF_1'('#skF_4','#skF_6',C_222,D_223))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_222,D_223),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_222,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_222,D_223),u1_struct_0('#skF_4'))
      | g1_orders_2(u1_struct_0('#skF_5'),u1_orders_2('#skF_5')) != g1_orders_2(u1_struct_0('#skF_4'),u1_orders_2('#skF_4'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden(D_223,'#skF_6')
      | ~ r2_hidden(C_222,'#skF_6')
      | ~ m1_subset_1(D_223,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_222,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_334])).

tff(c_364,plain,(
    ! [C_228,D_229] :
      ( r1_orders_2('#skF_5',C_228,'#skF_1'('#skF_4','#skF_6',C_228,D_229))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6',C_228,D_229),u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_229,'#skF_6')
      | ~ r2_hidden(C_228,'#skF_6')
      | ~ m1_subset_1(D_229,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_228,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_184,c_109,c_109,c_339])).

tff(c_367,plain,(
    ! [C_46,D_50] :
      ( r1_orders_2('#skF_5',C_46,'#skF_1'('#skF_4','#skF_6',C_46,D_50))
      | ~ r2_hidden(D_50,'#skF_6')
      | ~ r2_hidden(C_46,'#skF_6')
      | ~ m1_subset_1(D_50,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_46,u1_struct_0('#skF_4'))
      | ~ v1_waybel_0('#skF_6','#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_364])).

tff(c_377,plain,(
    ! [C_232,D_233] :
      ( r1_orders_2('#skF_5',C_232,'#skF_1'('#skF_4','#skF_6',C_232,D_233))
      | ~ r2_hidden(D_233,'#skF_6')
      | ~ r2_hidden(C_232,'#skF_6')
      | ~ m1_subset_1(D_233,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_232,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_32,c_367])).

tff(c_2,plain,(
    ! [A_1,B_31,E_56] :
      ( ~ r1_orders_2(A_1,'#skF_3'(A_1,B_31),E_56)
      | ~ r1_orders_2(A_1,'#skF_2'(A_1,B_31),E_56)
      | ~ r2_hidden(E_56,B_31)
      | ~ m1_subset_1(E_56,u1_struct_0(A_1))
      | v1_waybel_0(B_31,A_1)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_382,plain,(
    ! [B_31,D_233] :
      ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5',B_31),'#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_31),D_233))
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_31),D_233),B_31)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_31),D_233),u1_struct_0('#skF_5'))
      | v1_waybel_0(B_31,'#skF_5')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden(D_233,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_5',B_31),'#skF_6')
      | ~ m1_subset_1(D_233,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_31),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_377,c_2])).

tff(c_396,plain,(
    ! [B_235,D_236] :
      ( ~ r1_orders_2('#skF_5','#skF_2'('#skF_5',B_235),'#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_235),D_236))
      | ~ r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_235),D_236),B_235)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_235),D_236),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_235,'#skF_5')
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_236,'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_5',B_235),'#skF_6')
      | ~ m1_subset_1(D_236,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_235),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_109,c_109,c_382])).

tff(c_402,plain,(
    ! [B_237] :
      ( ~ r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_237),'#skF_2'('#skF_5',B_237)),B_237)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5',B_237),'#skF_2'('#skF_5',B_237)),u1_struct_0('#skF_4'))
      | v1_waybel_0(B_237,'#skF_5')
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_2'('#skF_5',B_237),'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_5',B_237),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_237),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_237),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_351,c_396])).

tff(c_405,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),u1_struct_0('#skF_4'))
    | v1_waybel_0('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_239,c_402])).

tff(c_408,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),u1_struct_0('#skF_4'))
    | v1_waybel_0('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_94,c_38,c_405])).

tff(c_409,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_408])).

tff(c_410,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_419,plain,
    ( v1_waybel_0('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_150,c_410])).

tff(c_422,plain,(
    v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_419])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_422])).

tff(c_426,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_425,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_427,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4','#skF_6','#skF_3'('#skF_5','#skF_6'),'#skF_2'('#skF_5','#skF_6')),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_430,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_waybel_0('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_427])).

tff(c_433,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_32,c_426,c_82,c_94,c_430])).

tff(c_436,plain,
    ( v1_waybel_0('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_148,c_433])).

tff(c_439,plain,(
    v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_436])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_439])).

tff(c_442,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_446,plain,
    ( v1_waybel_0('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_148,c_442])).

tff(c_449,plain,(
    v1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_446])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_449])).

%------------------------------------------------------------------------------
