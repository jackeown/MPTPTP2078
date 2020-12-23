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
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 624 expanded)
%              Number of leaves         :   44 ( 242 expanded)
%              Depth                    :   12
%              Number of atoms          :  286 (3058 expanded)
%              Number of equality atoms :   21 ( 345 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_244,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_195,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_124,plain,(
    ! [B_294,A_295] :
      ( l1_pre_topc(B_294)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_124])).

tff(c_136,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_130])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    ! [A_292] :
      ( u1_struct_0(A_292) = k2_struct_0(A_292)
      | ~ l1_struct_0(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_105])).

tff(c_106,plain,(
    ! [A_293] :
      ( u1_struct_0(A_293) = k2_struct_0(A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_106])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_119,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56])).

tff(c_153,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_119])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_151,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_54])).

tff(c_152,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_151])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_124])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_127])).

tff(c_140,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_105])).

tff(c_177,plain,(
    ! [B_299,A_300] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_183,plain,(
    ! [B_299] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_299,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_177])).

tff(c_210,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_183])).

tff(c_216,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_210])).

tff(c_318,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_145,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_52])).

tff(c_569,plain,(
    ! [A_324,B_325] :
      ( k1_tsep_1(A_324,B_325,B_325) = g1_pre_topc(u1_struct_0(B_325),u1_pre_topc(B_325))
      | ~ m1_pre_topc(B_325,A_324)
      | v2_struct_0(B_325)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_573,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_569])).

tff(c_581,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_145,c_140,c_573])).

tff(c_582,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_581])).

tff(c_723,plain,(
    ! [B_338,A_339,C_340] :
      ( m1_pre_topc(B_338,k1_tsep_1(A_339,B_338,C_340))
      | ~ m1_pre_topc(C_340,A_339)
      | v2_struct_0(C_340)
      | ~ m1_pre_topc(B_338,A_339)
      | v2_struct_0(B_338)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_744,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_723])).

tff(c_756,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_64,c_744])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_318,c_756])).

tff(c_760,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_164,plain,(
    ! [B_297,A_298] :
      ( v2_pre_topc(B_297)
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_164])).

tff(c_176,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_170])).

tff(c_167,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_164])).

tff(c_173,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_167])).

tff(c_22,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_281,plain,(
    ! [B_309,A_310] :
      ( v3_pre_topc(B_309,g1_pre_topc(u1_struct_0(A_310),u1_pre_topc(A_310)))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ v3_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_287,plain,(
    ! [B_309] :
      ( v3_pre_topc(B_309,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_309,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_281])).

tff(c_910,plain,(
    ! [B_347] :
      ( v3_pre_topc(B_347,'#skF_4')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_347,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_133,c_140,c_145,c_287])).

tff(c_919,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_910])).

tff(c_966,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_969,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_966])).

tff(c_973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_133,c_969])).

tff(c_974,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_30,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1045,plain,(
    ! [B_354,A_355] :
      ( v1_tsep_1(B_354,A_355)
      | ~ v3_pre_topc(u1_struct_0(B_354),A_355)
      | ~ m1_subset_1(u1_struct_0(B_354),k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_pre_topc(B_354,A_355)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1101,plain,(
    ! [B_357,A_358] :
      ( v1_tsep_1(B_357,A_358)
      | ~ v3_pre_topc(u1_struct_0(B_357),A_358)
      | ~ v2_pre_topc(A_358)
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(resolution,[status(thm)],[c_30,c_1045])).

tff(c_1322,plain,(
    ! [A_377] :
      ( v1_tsep_1('#skF_3',A_377)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_377)
      | ~ v2_pre_topc(A_377)
      | ~ m1_pre_topc('#skF_3',A_377)
      | ~ l1_pre_topc(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1101])).

tff(c_1331,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_974,c_1322])).

tff(c_1346,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_760,c_176,c_1331])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_154,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_146,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_79])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1893,plain,(
    ! [D_413,C_409,A_410,E_411,G_414,B_412] :
      ( r1_tmap_1(D_413,B_412,E_411,G_414)
      | ~ r1_tmap_1(C_409,B_412,k3_tmap_1(A_410,B_412,D_413,C_409,E_411),G_414)
      | ~ m1_subset_1(G_414,u1_struct_0(C_409))
      | ~ m1_subset_1(G_414,u1_struct_0(D_413))
      | ~ m1_pre_topc(C_409,D_413)
      | ~ v1_tsep_1(C_409,D_413)
      | ~ m1_subset_1(E_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413),u1_struct_0(B_412))))
      | ~ v1_funct_2(E_411,u1_struct_0(D_413),u1_struct_0(B_412))
      | ~ v1_funct_1(E_411)
      | ~ m1_pre_topc(D_413,A_410)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(C_409,A_410)
      | v2_struct_0(C_409)
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1895,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_1893])).

tff(c_1898,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_153,c_114,c_144,c_152,c_114,c_144,c_1346,c_760,c_154,c_144,c_146,c_140,c_1895])).

tff(c_1900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.81  
% 4.95/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.81  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.95/1.81  
% 4.95/1.81  %Foreground sorts:
% 4.95/1.81  
% 4.95/1.81  
% 4.95/1.81  %Background operators:
% 4.95/1.81  
% 4.95/1.81  
% 4.95/1.81  %Foreground operators:
% 4.95/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.95/1.81  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.95/1.81  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.95/1.81  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.95/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.95/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.95/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.81  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.95/1.81  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.95/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.95/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.95/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.95/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.95/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.95/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.95/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.95/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/1.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.95/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.95/1.81  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.95/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.95/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.95/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.95/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.95/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.95/1.81  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.95/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/1.81  
% 5.07/1.83  tff(f_244, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.07/1.83  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.07/1.83  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.07/1.83  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.07/1.83  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.07/1.83  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 5.07/1.83  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 5.07/1.83  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.07/1.83  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.07/1.83  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.07/1.83  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.07/1.83  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 5.07/1.83  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.07/1.83  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.07/1.83  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_124, plain, (![B_294, A_295]: (l1_pre_topc(B_294) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.07/1.83  tff(c_130, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_124])).
% 5.07/1.83  tff(c_136, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_130])).
% 5.07/1.83  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.07/1.83  tff(c_101, plain, (![A_292]: (u1_struct_0(A_292)=k2_struct_0(A_292) | ~l1_struct_0(A_292))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.07/1.83  tff(c_105, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_101])).
% 5.07/1.83  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_136, c_105])).
% 5.07/1.83  tff(c_106, plain, (![A_293]: (u1_struct_0(A_293)=k2_struct_0(A_293) | ~l1_pre_topc(A_293))), inference(resolution, [status(thm)], [c_10, c_101])).
% 5.07/1.83  tff(c_114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_106])).
% 5.07/1.83  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_119, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56])).
% 5.07/1.83  tff(c_153, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_119])).
% 5.07/1.83  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_54])).
% 5.07/1.83  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_151])).
% 5.07/1.83  tff(c_127, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_124])).
% 5.07/1.83  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_127])).
% 5.07/1.83  tff(c_140, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_105])).
% 5.07/1.83  tff(c_177, plain, (![B_299, A_300]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(u1_struct_0(A_300))) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.83  tff(c_183, plain, (![B_299]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_299, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_177])).
% 5.07/1.83  tff(c_210, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_183])).
% 5.07/1.83  tff(c_216, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_210])).
% 5.07/1.83  tff(c_318, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 5.07/1.83  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_145, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_52])).
% 5.07/1.83  tff(c_569, plain, (![A_324, B_325]: (k1_tsep_1(A_324, B_325, B_325)=g1_pre_topc(u1_struct_0(B_325), u1_pre_topc(B_325)) | ~m1_pre_topc(B_325, A_324) | v2_struct_0(B_325) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.07/1.83  tff(c_573, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_569])).
% 5.07/1.83  tff(c_581, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_145, c_140, c_573])).
% 5.07/1.83  tff(c_582, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_581])).
% 5.07/1.83  tff(c_723, plain, (![B_338, A_339, C_340]: (m1_pre_topc(B_338, k1_tsep_1(A_339, B_338, C_340)) | ~m1_pre_topc(C_340, A_339) | v2_struct_0(C_340) | ~m1_pre_topc(B_338, A_339) | v2_struct_0(B_338) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.83  tff(c_744, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_582, c_723])).
% 5.07/1.83  tff(c_756, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_64, c_744])).
% 5.07/1.83  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_318, c_756])).
% 5.07/1.83  tff(c_760, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_216])).
% 5.07/1.83  tff(c_164, plain, (![B_297, A_298]: (v2_pre_topc(B_297) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/1.83  tff(c_170, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_164])).
% 5.07/1.83  tff(c_176, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_170])).
% 5.07/1.83  tff(c_167, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_164])).
% 5.07/1.83  tff(c_173, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_167])).
% 5.07/1.83  tff(c_22, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.07/1.83  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/1.83  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.07/1.83  tff(c_81, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.07/1.83  tff(c_281, plain, (![B_309, A_310]: (v3_pre_topc(B_309, g1_pre_topc(u1_struct_0(A_310), u1_pre_topc(A_310))) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_310))) | ~v3_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.07/1.83  tff(c_287, plain, (![B_309]: (v3_pre_topc(B_309, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_309, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_281])).
% 5.07/1.83  tff(c_910, plain, (![B_347]: (v3_pre_topc(B_347, '#skF_4') | ~m1_subset_1(B_347, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_347, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_133, c_140, c_145, c_287])).
% 5.07/1.83  tff(c_919, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_81, c_910])).
% 5.07/1.83  tff(c_966, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_919])).
% 5.07/1.83  tff(c_969, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_966])).
% 5.07/1.83  tff(c_973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_133, c_969])).
% 5.07/1.83  tff(c_974, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_919])).
% 5.07/1.83  tff(c_30, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.07/1.83  tff(c_1045, plain, (![B_354, A_355]: (v1_tsep_1(B_354, A_355) | ~v3_pre_topc(u1_struct_0(B_354), A_355) | ~m1_subset_1(u1_struct_0(B_354), k1_zfmisc_1(u1_struct_0(A_355))) | ~m1_pre_topc(B_354, A_355) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.07/1.83  tff(c_1101, plain, (![B_357, A_358]: (v1_tsep_1(B_357, A_358) | ~v3_pre_topc(u1_struct_0(B_357), A_358) | ~v2_pre_topc(A_358) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358))), inference(resolution, [status(thm)], [c_30, c_1045])).
% 5.07/1.83  tff(c_1322, plain, (![A_377]: (v1_tsep_1('#skF_3', A_377) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_377) | ~v2_pre_topc(A_377) | ~m1_pre_topc('#skF_3', A_377) | ~l1_pre_topc(A_377))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1101])).
% 5.07/1.83  tff(c_1331, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_974, c_1322])).
% 5.07/1.83  tff(c_1346, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_760, c_176, c_1331])).
% 5.07/1.83  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_154, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_50])).
% 5.07/1.83  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 5.07/1.83  tff(c_146, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_79])).
% 5.07/1.83  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.83  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.07/1.83  tff(c_1893, plain, (![D_413, C_409, A_410, E_411, G_414, B_412]: (r1_tmap_1(D_413, B_412, E_411, G_414) | ~r1_tmap_1(C_409, B_412, k3_tmap_1(A_410, B_412, D_413, C_409, E_411), G_414) | ~m1_subset_1(G_414, u1_struct_0(C_409)) | ~m1_subset_1(G_414, u1_struct_0(D_413)) | ~m1_pre_topc(C_409, D_413) | ~v1_tsep_1(C_409, D_413) | ~m1_subset_1(E_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413), u1_struct_0(B_412)))) | ~v1_funct_2(E_411, u1_struct_0(D_413), u1_struct_0(B_412)) | ~v1_funct_1(E_411) | ~m1_pre_topc(D_413, A_410) | v2_struct_0(D_413) | ~m1_pre_topc(C_409, A_410) | v2_struct_0(C_409) | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | ~l1_pre_topc(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410))), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.07/1.83  tff(c_1895, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_1893])).
% 5.07/1.83  tff(c_1898, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_153, c_114, c_144, c_152, c_114, c_144, c_1346, c_760, c_154, c_144, c_146, c_140, c_1895])).
% 5.07/1.83  tff(c_1900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1898])).
% 5.07/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.83  
% 5.07/1.83  Inference rules
% 5.07/1.83  ----------------------
% 5.07/1.83  #Ref     : 0
% 5.07/1.83  #Sup     : 373
% 5.07/1.83  #Fact    : 0
% 5.07/1.83  #Define  : 0
% 5.07/1.83  #Split   : 25
% 5.07/1.83  #Chain   : 0
% 5.07/1.83  #Close   : 0
% 5.07/1.83  
% 5.07/1.83  Ordering : KBO
% 5.07/1.83  
% 5.07/1.83  Simplification rules
% 5.07/1.83  ----------------------
% 5.07/1.83  #Subsume      : 89
% 5.07/1.83  #Demod        : 455
% 5.07/1.83  #Tautology    : 85
% 5.07/1.83  #SimpNegUnit  : 29
% 5.07/1.83  #BackRed      : 6
% 5.07/1.83  
% 5.07/1.83  #Partial instantiations: 0
% 5.07/1.83  #Strategies tried      : 1
% 5.07/1.83  
% 5.07/1.83  Timing (in seconds)
% 5.07/1.83  ----------------------
% 5.07/1.83  Preprocessing        : 0.40
% 5.07/1.83  Parsing              : 0.20
% 5.07/1.83  CNF conversion       : 0.05
% 5.07/1.83  Main loop            : 0.65
% 5.07/1.83  Inferencing          : 0.20
% 5.07/1.83  Reduction            : 0.23
% 5.07/1.83  Demodulation         : 0.17
% 5.07/1.84  BG Simplification    : 0.03
% 5.07/1.84  Subsumption          : 0.13
% 5.07/1.84  Abstraction          : 0.04
% 5.07/1.84  MUC search           : 0.00
% 5.07/1.84  Cooper               : 0.00
% 5.07/1.84  Total                : 1.10
% 5.07/1.84  Index Insertion      : 0.00
% 5.07/1.84  Index Deletion       : 0.00
% 5.07/1.84  Index Matching       : 0.00
% 5.07/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
