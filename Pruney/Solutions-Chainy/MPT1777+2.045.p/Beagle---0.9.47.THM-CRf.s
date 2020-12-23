%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 746 expanded)
%              Number of leaves         :   43 ( 275 expanded)
%              Depth                    :   16
%              Number of atoms          :  266 (3309 expanded)
%              Number of equality atoms :   19 ( 371 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_172,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_118,plain,(
    ! [B_290,A_291] :
      ( l1_pre_topc(B_290)
      | ~ m1_pre_topc(B_290,A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_118])).

tff(c_134,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,(
    ! [A_288] :
      ( u1_struct_0(A_288) = k2_struct_0(A_288)
      | ~ l1_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_142,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_95])).

tff(c_100,plain,(
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_pre_topc(A_289) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_108,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_100])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_113,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_58])).

tff(c_151,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_113])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_149,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_56])).

tff(c_150,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_149])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_131,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_124])).

tff(c_138,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_199,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_208,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_199])).

tff(c_236,plain,(
    ! [B_303] :
      ( m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_303,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_208])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_253,plain,(
    ! [B_304] :
      ( r1_tarski(u1_struct_0(B_304),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_304,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_236,c_8])).

tff(c_261,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_253])).

tff(c_270,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_36,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_143,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_54])).

tff(c_479,plain,(
    ! [A_318,B_319] :
      ( m1_pre_topc(A_318,g1_pre_topc(u1_struct_0(B_319),u1_pre_topc(B_319)))
      | ~ m1_pre_topc(A_318,B_319)
      | ~ l1_pre_topc(B_319)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_496,plain,(
    ! [A_318] :
      ( m1_pre_topc(A_318,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_318,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_479])).

tff(c_515,plain,(
    ! [A_320] :
      ( m1_pre_topc(A_320,'#skF_4')
      | ~ m1_pre_topc(A_320,'#skF_3')
      | ~ l1_pre_topc(A_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_143,c_496])).

tff(c_526,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_515])).

tff(c_534,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_526])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_534])).

tff(c_538,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_152,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_52])).

tff(c_537,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_577,plain,(
    ! [B_322,A_323] :
      ( m1_pre_topc(B_322,A_323)
      | ~ m1_pre_topc(B_322,g1_pre_topc(u1_struct_0(A_323),u1_pre_topc(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_583,plain,(
    ! [B_322] :
      ( m1_pre_topc(B_322,'#skF_3')
      | ~ m1_pre_topc(B_322,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_577])).

tff(c_597,plain,(
    ! [B_322] :
      ( m1_pre_topc(B_322,'#skF_3')
      | ~ m1_pre_topc(B_322,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_143,c_583])).

tff(c_214,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_301,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_199])).

tff(c_694,plain,(
    ! [B_331] :
      ( m1_subset_1(u1_struct_0(B_331),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_331,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_214])).

tff(c_711,plain,(
    ! [B_332] :
      ( r1_tarski(u1_struct_0(B_332),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_332,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_694,c_8])).

tff(c_716,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_711])).

tff(c_753,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_800,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_597,c_753])).

tff(c_803,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_800])).

tff(c_807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_803])).

tff(c_808,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_859,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_808,c_2])).

tff(c_862,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_859])).

tff(c_871,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_138])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1246,plain,(
    ! [G_349,B_350,A_347,E_351,D_352,C_348] :
      ( r1_tmap_1(D_352,B_350,E_351,G_349)
      | ~ r1_tmap_1(C_348,B_350,k3_tmap_1(A_347,B_350,D_352,C_348,E_351),G_349)
      | ~ m1_subset_1(G_349,u1_struct_0(C_348))
      | ~ m1_subset_1(G_349,u1_struct_0(D_352))
      | ~ m1_pre_topc(C_348,D_352)
      | ~ v1_tsep_1(C_348,D_352)
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_352),u1_struct_0(B_350))))
      | ~ v1_funct_2(E_351,u1_struct_0(D_352),u1_struct_0(B_350))
      | ~ v1_funct_1(E_351)
      | ~ m1_pre_topc(D_352,A_347)
      | v2_struct_0(D_352)
      | ~ m1_pre_topc(C_348,A_347)
      | v2_struct_0(C_348)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1248,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1246])).

tff(c_1251,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_151,c_108,c_142,c_150,c_108,c_142,c_538,c_152,c_142,c_152,c_871,c_1248])).

tff(c_1252,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1251])).

tff(c_182,plain,(
    ! [B_299,A_300] :
      ( v2_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_182])).

tff(c_198,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_191])).

tff(c_26,plain,(
    ! [A_19] :
      ( v3_pre_topc(k2_struct_0(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1080,plain,(
    ! [B_343,A_344] :
      ( v1_tsep_1(B_343,A_344)
      | ~ v3_pre_topc(u1_struct_0(B_343),A_344)
      | ~ m1_subset_1(u1_struct_0(B_343),k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ m1_pre_topc(B_343,A_344)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1718,plain,(
    ! [B_385,A_386] :
      ( v1_tsep_1(B_385,A_386)
      | ~ v3_pre_topc(u1_struct_0(B_385),A_386)
      | ~ v2_pre_topc(A_386)
      | ~ m1_pre_topc(B_385,A_386)
      | ~ l1_pre_topc(A_386) ) ),
    inference(resolution,[status(thm)],[c_34,c_1080])).

tff(c_2929,plain,(
    ! [A_464] :
      ( v1_tsep_1('#skF_3',A_464)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_464)
      | ~ v2_pre_topc(A_464)
      | ~ m1_pre_topc('#skF_3',A_464)
      | ~ l1_pre_topc(A_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_1718])).

tff(c_2939,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2929])).

tff(c_2946,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_134,c_538,c_2939])).

tff(c_2948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1252,c_2946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.03  
% 5.52/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.04  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.52/2.04  
% 5.52/2.04  %Foreground sorts:
% 5.52/2.04  
% 5.52/2.04  
% 5.52/2.04  %Background operators:
% 5.52/2.04  
% 5.52/2.04  
% 5.52/2.04  %Foreground operators:
% 5.52/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.52/2.04  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.52/2.04  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.52/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.52/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.52/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.04  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.52/2.04  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.52/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.52/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.52/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.52/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.52/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.52/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.52/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.52/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.04  tff('#skF_1', type, '#skF_1': $i).
% 5.52/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.52/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.04  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.52/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.52/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.04  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.52/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.52/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.52/2.04  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.52/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.04  
% 5.52/2.06  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.52/2.06  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.52/2.06  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.52/2.06  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.52/2.06  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.52/2.06  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.52/2.06  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.52/2.06  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.52/2.06  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.52/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.52/2.06  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.52/2.06  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.52/2.06  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.52/2.06  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.52/2.06  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_118, plain, (![B_290, A_291]: (l1_pre_topc(B_290) | ~m1_pre_topc(B_290, A_291) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.06  tff(c_127, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_118])).
% 5.52/2.06  tff(c_134, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_127])).
% 5.52/2.06  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.52/2.06  tff(c_91, plain, (![A_288]: (u1_struct_0(A_288)=k2_struct_0(A_288) | ~l1_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.52/2.06  tff(c_95, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_91])).
% 5.52/2.06  tff(c_142, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_134, c_95])).
% 5.52/2.06  tff(c_100, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_pre_topc(A_289))), inference(resolution, [status(thm)], [c_16, c_91])).
% 5.52/2.06  tff(c_108, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_100])).
% 5.52/2.06  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_113, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_58])).
% 5.52/2.06  tff(c_151, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_113])).
% 5.52/2.06  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_149, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_56])).
% 5.52/2.06  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_149])).
% 5.52/2.06  tff(c_124, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_118])).
% 5.52/2.06  tff(c_131, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_124])).
% 5.52/2.06  tff(c_138, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_131, c_95])).
% 5.52/2.06  tff(c_199, plain, (![B_301, A_302]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(u1_struct_0(A_302))) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.52/2.06  tff(c_208, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_199])).
% 5.52/2.06  tff(c_236, plain, (![B_303]: (m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_303, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_208])).
% 5.52/2.06  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.06  tff(c_253, plain, (![B_304]: (r1_tarski(u1_struct_0(B_304), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_304, '#skF_4'))), inference(resolution, [status(thm)], [c_236, c_8])).
% 5.52/2.06  tff(c_261, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_253])).
% 5.52/2.06  tff(c_270, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_261])).
% 5.52/2.06  tff(c_36, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.52/2.06  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_143, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_54])).
% 5.52/2.06  tff(c_479, plain, (![A_318, B_319]: (m1_pre_topc(A_318, g1_pre_topc(u1_struct_0(B_319), u1_pre_topc(B_319))) | ~m1_pre_topc(A_318, B_319) | ~l1_pre_topc(B_319) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.52/2.06  tff(c_496, plain, (![A_318]: (m1_pre_topc(A_318, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_318, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_318))), inference(superposition, [status(thm), theory('equality')], [c_138, c_479])).
% 5.52/2.06  tff(c_515, plain, (![A_320]: (m1_pre_topc(A_320, '#skF_4') | ~m1_pre_topc(A_320, '#skF_3') | ~l1_pre_topc(A_320))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_143, c_496])).
% 5.52/2.06  tff(c_526, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_515])).
% 5.52/2.06  tff(c_534, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_526])).
% 5.52/2.06  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_534])).
% 5.52/2.06  tff(c_538, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_261])).
% 5.52/2.06  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_152, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_52])).
% 5.52/2.06  tff(c_537, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_261])).
% 5.52/2.06  tff(c_577, plain, (![B_322, A_323]: (m1_pre_topc(B_322, A_323) | ~m1_pre_topc(B_322, g1_pre_topc(u1_struct_0(A_323), u1_pre_topc(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.52/2.06  tff(c_583, plain, (![B_322]: (m1_pre_topc(B_322, '#skF_3') | ~m1_pre_topc(B_322, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_577])).
% 5.52/2.06  tff(c_597, plain, (![B_322]: (m1_pre_topc(B_322, '#skF_3') | ~m1_pre_topc(B_322, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_143, c_583])).
% 5.52/2.06  tff(c_214, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_301, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_199])).
% 5.52/2.06  tff(c_694, plain, (![B_331]: (m1_subset_1(u1_struct_0(B_331), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_331, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_214])).
% 5.52/2.06  tff(c_711, plain, (![B_332]: (r1_tarski(u1_struct_0(B_332), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_332, '#skF_3'))), inference(resolution, [status(thm)], [c_694, c_8])).
% 5.52/2.06  tff(c_716, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_711])).
% 5.52/2.06  tff(c_753, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_716])).
% 5.52/2.06  tff(c_800, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_597, c_753])).
% 5.52/2.06  tff(c_803, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_800])).
% 5.52/2.06  tff(c_807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_803])).
% 5.52/2.06  tff(c_808, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_716])).
% 5.52/2.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.52/2.06  tff(c_859, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_808, c_2])).
% 5.52/2.06  tff(c_862, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_859])).
% 5.52/2.06  tff(c_871, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_138])).
% 5.52/2.06  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.52/2.06  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.52/2.06  tff(c_1246, plain, (![G_349, B_350, A_347, E_351, D_352, C_348]: (r1_tmap_1(D_352, B_350, E_351, G_349) | ~r1_tmap_1(C_348, B_350, k3_tmap_1(A_347, B_350, D_352, C_348, E_351), G_349) | ~m1_subset_1(G_349, u1_struct_0(C_348)) | ~m1_subset_1(G_349, u1_struct_0(D_352)) | ~m1_pre_topc(C_348, D_352) | ~v1_tsep_1(C_348, D_352) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_352), u1_struct_0(B_350)))) | ~v1_funct_2(E_351, u1_struct_0(D_352), u1_struct_0(B_350)) | ~v1_funct_1(E_351) | ~m1_pre_topc(D_352, A_347) | v2_struct_0(D_352) | ~m1_pre_topc(C_348, A_347) | v2_struct_0(C_348) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.52/2.06  tff(c_1248, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1246])).
% 5.52/2.06  tff(c_1251, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_151, c_108, c_142, c_150, c_108, c_142, c_538, c_152, c_142, c_152, c_871, c_1248])).
% 5.52/2.06  tff(c_1252, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1251])).
% 5.52/2.06  tff(c_182, plain, (![B_299, A_300]: (v2_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.52/2.06  tff(c_191, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_182])).
% 5.52/2.06  tff(c_198, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_191])).
% 5.52/2.06  tff(c_26, plain, (![A_19]: (v3_pre_topc(k2_struct_0(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.52/2.06  tff(c_34, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.52/2.06  tff(c_1080, plain, (![B_343, A_344]: (v1_tsep_1(B_343, A_344) | ~v3_pre_topc(u1_struct_0(B_343), A_344) | ~m1_subset_1(u1_struct_0(B_343), k1_zfmisc_1(u1_struct_0(A_344))) | ~m1_pre_topc(B_343, A_344) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.52/2.06  tff(c_1718, plain, (![B_385, A_386]: (v1_tsep_1(B_385, A_386) | ~v3_pre_topc(u1_struct_0(B_385), A_386) | ~v2_pre_topc(A_386) | ~m1_pre_topc(B_385, A_386) | ~l1_pre_topc(A_386))), inference(resolution, [status(thm)], [c_34, c_1080])).
% 5.52/2.06  tff(c_2929, plain, (![A_464]: (v1_tsep_1('#skF_3', A_464) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_464) | ~v2_pre_topc(A_464) | ~m1_pre_topc('#skF_3', A_464) | ~l1_pre_topc(A_464))), inference(superposition, [status(thm), theory('equality')], [c_871, c_1718])).
% 5.52/2.06  tff(c_2939, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2929])).
% 5.52/2.06  tff(c_2946, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_134, c_538, c_2939])).
% 5.52/2.06  tff(c_2948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1252, c_2946])).
% 5.52/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.06  
% 5.52/2.06  Inference rules
% 5.52/2.06  ----------------------
% 5.52/2.06  #Ref     : 0
% 5.52/2.06  #Sup     : 586
% 5.52/2.06  #Fact    : 0
% 5.52/2.06  #Define  : 0
% 5.52/2.06  #Split   : 22
% 5.52/2.06  #Chain   : 0
% 5.52/2.06  #Close   : 0
% 5.52/2.06  
% 5.52/2.06  Ordering : KBO
% 5.52/2.06  
% 5.52/2.06  Simplification rules
% 5.52/2.06  ----------------------
% 5.52/2.06  #Subsume      : 166
% 5.52/2.06  #Demod        : 837
% 5.52/2.06  #Tautology    : 180
% 5.52/2.06  #SimpNegUnit  : 32
% 5.52/2.06  #BackRed      : 15
% 5.52/2.06  
% 5.52/2.06  #Partial instantiations: 0
% 5.52/2.06  #Strategies tried      : 1
% 5.52/2.06  
% 5.52/2.06  Timing (in seconds)
% 5.52/2.06  ----------------------
% 5.52/2.06  Preprocessing        : 0.40
% 5.52/2.06  Parsing              : 0.20
% 5.52/2.06  CNF conversion       : 0.05
% 5.52/2.06  Main loop            : 0.84
% 5.52/2.06  Inferencing          : 0.28
% 5.52/2.06  Reduction            : 0.30
% 5.52/2.06  Demodulation         : 0.22
% 5.52/2.06  BG Simplification    : 0.03
% 5.52/2.06  Subsumption          : 0.18
% 5.52/2.06  Abstraction          : 0.03
% 5.52/2.06  MUC search           : 0.00
% 5.52/2.06  Cooper               : 0.00
% 5.52/2.06  Total                : 1.28
% 5.52/2.06  Index Insertion      : 0.00
% 5.52/2.06  Index Deletion       : 0.00
% 5.52/2.06  Index Matching       : 0.00
% 5.52/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
