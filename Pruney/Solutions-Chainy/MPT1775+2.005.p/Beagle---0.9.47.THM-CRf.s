%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 281 expanded)
%              Number of leaves         :   43 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  393 (1951 expanded)
%              Number of equality atoms :    6 (  84 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_286,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_113,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_235,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_180,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_46,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_100,plain,(
    ! [B_560,A_561] :
      ( l1_pre_topc(B_560)
      | ~ m1_pre_topc(B_560,A_561)
      | ~ l1_pre_topc(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_109])).

tff(c_127,plain,(
    ! [B_566,A_567] :
      ( v2_pre_topc(B_566)
      | ~ m1_pre_topc(B_566,A_567)
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_145,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_136])).

tff(c_54,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_36,plain,(
    ! [B_47,A_45] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_262,plain,(
    ! [B_590,A_591] :
      ( v3_pre_topc(u1_struct_0(B_590),A_591)
      | ~ v1_tsep_1(B_590,A_591)
      | ~ m1_subset_1(u1_struct_0(B_590),k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ m1_pre_topc(B_590,A_591)
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_266,plain,(
    ! [B_47,A_45] :
      ( v3_pre_topc(u1_struct_0(B_47),A_45)
      | ~ v1_tsep_1(B_47,A_45)
      | ~ v2_pre_topc(A_45)
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_36,c_262])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_112,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_103])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [B_572,A_573] :
      ( m1_subset_1(u1_struct_0(B_572),k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ m1_pre_topc(B_572,A_573)
      | ~ l1_pre_topc(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,(
    ! [A_580,A_581,B_582] :
      ( m1_subset_1(A_580,u1_struct_0(A_581))
      | ~ r2_hidden(A_580,u1_struct_0(B_582))
      | ~ m1_pre_topc(B_582,A_581)
      | ~ l1_pre_topc(A_581) ) ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_200,plain,(
    ! [A_583,A_584,B_585] :
      ( m1_subset_1(A_583,u1_struct_0(A_584))
      | ~ m1_pre_topc(B_585,A_584)
      | ~ l1_pre_topc(A_584)
      | v1_xboole_0(u1_struct_0(B_585))
      | ~ m1_subset_1(A_583,u1_struct_0(B_585)) ) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_204,plain,(
    ! [A_583] :
      ( m1_subset_1(A_583,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_583,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_200])).

tff(c_212,plain,(
    ! [A_583] :
      ( m1_subset_1(A_583,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_583,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_204])).

tff(c_219,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_18,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_222,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_18])).

tff(c_225,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_222])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_225])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_233])).

tff(c_239,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_377,plain,(
    ! [C_631,A_632,B_633,D_634] :
      ( m1_connsp_2(C_631,A_632,B_633)
      | ~ r2_hidden(B_633,D_634)
      | ~ r1_tarski(D_634,C_631)
      | ~ v3_pre_topc(D_634,A_632)
      | ~ m1_subset_1(D_634,k1_zfmisc_1(u1_struct_0(A_632)))
      | ~ m1_subset_1(C_631,k1_zfmisc_1(u1_struct_0(A_632)))
      | ~ m1_subset_1(B_633,u1_struct_0(A_632))
      | ~ l1_pre_topc(A_632)
      | ~ v2_pre_topc(A_632)
      | v2_struct_0(A_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_399,plain,(
    ! [C_648,A_649,A_650,B_651] :
      ( m1_connsp_2(C_648,A_649,A_650)
      | ~ r1_tarski(B_651,C_648)
      | ~ v3_pre_topc(B_651,A_649)
      | ~ m1_subset_1(B_651,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ m1_subset_1(C_648,k1_zfmisc_1(u1_struct_0(A_649)))
      | ~ m1_subset_1(A_650,u1_struct_0(A_649))
      | ~ l1_pre_topc(A_649)
      | ~ v2_pre_topc(A_649)
      | v2_struct_0(A_649)
      | v1_xboole_0(B_651)
      | ~ m1_subset_1(A_650,B_651) ) ),
    inference(resolution,[status(thm)],[c_8,c_377])).

tff(c_407,plain,(
    ! [B_655,A_656,A_657] :
      ( m1_connsp_2(B_655,A_656,A_657)
      | ~ v3_pre_topc(B_655,A_656)
      | ~ m1_subset_1(B_655,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ m1_subset_1(A_657,u1_struct_0(A_656))
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | v2_struct_0(A_656)
      | v1_xboole_0(B_655)
      | ~ m1_subset_1(A_657,B_655) ) ),
    inference(resolution,[status(thm)],[c_6,c_399])).

tff(c_413,plain,(
    ! [B_47,A_45,A_657] :
      ( m1_connsp_2(u1_struct_0(B_47),A_45,A_657)
      | ~ v3_pre_topc(u1_struct_0(B_47),A_45)
      | ~ m1_subset_1(A_657,u1_struct_0(A_45))
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | v1_xboole_0(u1_struct_0(B_47))
      | ~ m1_subset_1(A_657,u1_struct_0(B_47))
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_36,c_407])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_146,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_88])).

tff(c_199,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_89])).

tff(c_424,plain,(
    ! [D_674,E_677,C_673,A_678,H_676,F_675,B_679] :
      ( r1_tmap_1(D_674,B_679,E_677,H_676)
      | ~ r1_tmap_1(C_673,B_679,k3_tmap_1(A_678,B_679,D_674,C_673,E_677),H_676)
      | ~ m1_connsp_2(F_675,D_674,H_676)
      | ~ r1_tarski(F_675,u1_struct_0(C_673))
      | ~ m1_subset_1(H_676,u1_struct_0(C_673))
      | ~ m1_subset_1(H_676,u1_struct_0(D_674))
      | ~ m1_subset_1(F_675,k1_zfmisc_1(u1_struct_0(D_674)))
      | ~ m1_pre_topc(C_673,D_674)
      | ~ m1_subset_1(E_677,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_674),u1_struct_0(B_679))))
      | ~ v1_funct_2(E_677,u1_struct_0(D_674),u1_struct_0(B_679))
      | ~ v1_funct_1(E_677)
      | ~ m1_pre_topc(D_674,A_678)
      | v2_struct_0(D_674)
      | ~ m1_pre_topc(C_673,A_678)
      | v2_struct_0(C_673)
      | ~ l1_pre_topc(B_679)
      | ~ v2_pre_topc(B_679)
      | v2_struct_0(B_679)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_428,plain,(
    ! [F_675] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_675,'#skF_5','#skF_8')
      | ~ r1_tarski(F_675,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_675,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_199,c_424])).

tff(c_435,plain,(
    ! [F_675] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_675,'#skF_5','#skF_8')
      | ~ r1_tarski(F_675,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_675,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_58,c_56,c_52,c_91,c_48,c_428])).

tff(c_437,plain,(
    ! [F_680] :
      ( ~ m1_connsp_2(F_680,'#skF_5','#skF_8')
      | ~ r1_tarski(F_680,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_680,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_146,c_435])).

tff(c_445,plain,(
    ! [B_47] :
      ( ~ m1_connsp_2(u1_struct_0(B_47),'#skF_5','#skF_8')
      | ~ r1_tarski(u1_struct_0(B_47),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_47,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_437])).

tff(c_453,plain,(
    ! [B_681] :
      ( ~ m1_connsp_2(u1_struct_0(B_681),'#skF_5','#skF_8')
      | ~ r1_tarski(u1_struct_0(B_681),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_681,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_445])).

tff(c_457,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_453])).

tff(c_460,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_457])).

tff(c_463,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_413,c_460])).

tff(c_466,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_52,c_48,c_145,c_91,c_463])).

tff(c_467,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_64,c_466])).

tff(c_470,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_266,c_467])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_52,c_145,c_54,c_470])).

tff(c_476,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_730,plain,(
    ! [C_763,D_761,A_764,G_762,B_760,E_765] :
      ( r1_tmap_1(D_761,B_760,k3_tmap_1(A_764,B_760,C_763,D_761,E_765),G_762)
      | ~ r1_tmap_1(C_763,B_760,E_765,G_762)
      | ~ m1_pre_topc(D_761,C_763)
      | ~ m1_subset_1(G_762,u1_struct_0(D_761))
      | ~ m1_subset_1(G_762,u1_struct_0(C_763))
      | ~ m1_subset_1(E_765,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_763),u1_struct_0(B_760))))
      | ~ v1_funct_2(E_765,u1_struct_0(C_763),u1_struct_0(B_760))
      | ~ v1_funct_1(E_765)
      | ~ m1_pre_topc(D_761,A_764)
      | v2_struct_0(D_761)
      | ~ m1_pre_topc(C_763,A_764)
      | v2_struct_0(C_763)
      | ~ l1_pre_topc(B_760)
      | ~ v2_pre_topc(B_760)
      | v2_struct_0(B_760)
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_732,plain,(
    ! [D_761,A_764,G_762] :
      ( r1_tmap_1(D_761,'#skF_3',k3_tmap_1(A_764,'#skF_3','#skF_5',D_761,'#skF_6'),G_762)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_762)
      | ~ m1_pre_topc(D_761,'#skF_5')
      | ~ m1_subset_1(G_762,u1_struct_0(D_761))
      | ~ m1_subset_1(G_762,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_761,A_764)
      | v2_struct_0(D_761)
      | ~ m1_pre_topc('#skF_5',A_764)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(resolution,[status(thm)],[c_56,c_730])).

tff(c_735,plain,(
    ! [D_761,A_764,G_762] :
      ( r1_tmap_1(D_761,'#skF_3',k3_tmap_1(A_764,'#skF_3','#skF_5',D_761,'#skF_6'),G_762)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_762)
      | ~ m1_pre_topc(D_761,'#skF_5')
      | ~ m1_subset_1(G_762,u1_struct_0(D_761))
      | ~ m1_subset_1(G_762,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_761,A_764)
      | v2_struct_0(D_761)
      | ~ m1_pre_topc('#skF_5',A_764)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_58,c_732])).

tff(c_755,plain,(
    ! [D_791,A_792,G_793] :
      ( r1_tmap_1(D_791,'#skF_3',k3_tmap_1(A_792,'#skF_3','#skF_5',D_791,'#skF_6'),G_793)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_793)
      | ~ m1_pre_topc(D_791,'#skF_5')
      | ~ m1_subset_1(G_793,u1_struct_0(D_791))
      | ~ m1_subset_1(G_793,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_791,A_792)
      | v2_struct_0(D_791)
      | ~ m1_pre_topc('#skF_5',A_792)
      | ~ l1_pre_topc(A_792)
      | ~ v2_pre_topc(A_792)
      | v2_struct_0(A_792) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64,c_735])).

tff(c_475,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_760,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_755,c_475])).

tff(c_767,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_91,c_48,c_52,c_476,c_760])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68,c_767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.60  
% 4.01/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.60  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 4.01/1.60  
% 4.01/1.60  %Foreground sorts:
% 4.01/1.60  
% 4.01/1.60  
% 4.01/1.60  %Background operators:
% 4.01/1.60  
% 4.01/1.60  
% 4.01/1.60  %Foreground operators:
% 4.01/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.01/1.60  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.01/1.60  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.01/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.01/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.01/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.01/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.60  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.01/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.01/1.60  tff('#skF_7', type, '#skF_7': $i).
% 4.01/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.60  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.01/1.60  tff('#skF_6', type, '#skF_6': $i).
% 4.01/1.60  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.60  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.01/1.60  tff('#skF_8', type, '#skF_8': $i).
% 4.01/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.01/1.60  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.01/1.60  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.01/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.01/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.60  
% 4.01/1.62  tff(f_286, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.01/1.62  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.01/1.62  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.01/1.62  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.01/1.62  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.01/1.62  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.01/1.62  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.01/1.62  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.01/1.62  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.01/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.01/1.62  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.01/1.62  tff(f_235, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.01/1.62  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.01/1.62  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_46, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 4.01/1.62  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_100, plain, (![B_560, A_561]: (l1_pre_topc(B_560) | ~m1_pre_topc(B_560, A_561) | ~l1_pre_topc(A_561))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.01/1.62  tff(c_109, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_100])).
% 4.01/1.62  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_109])).
% 4.01/1.62  tff(c_127, plain, (![B_566, A_567]: (v2_pre_topc(B_566) | ~m1_pre_topc(B_566, A_567) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.01/1.62  tff(c_136, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_127])).
% 4.01/1.62  tff(c_145, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_136])).
% 4.01/1.62  tff(c_54, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_36, plain, (![B_47, A_45]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.62  tff(c_262, plain, (![B_590, A_591]: (v3_pre_topc(u1_struct_0(B_590), A_591) | ~v1_tsep_1(B_590, A_591) | ~m1_subset_1(u1_struct_0(B_590), k1_zfmisc_1(u1_struct_0(A_591))) | ~m1_pre_topc(B_590, A_591) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.01/1.62  tff(c_266, plain, (![B_47, A_45]: (v3_pre_topc(u1_struct_0(B_47), A_45) | ~v1_tsep_1(B_47, A_45) | ~v2_pre_topc(A_45) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_36, c_262])).
% 4.01/1.62  tff(c_103, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_100])).
% 4.01/1.62  tff(c_112, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_103])).
% 4.01/1.62  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.01/1.62  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.01/1.62  tff(c_154, plain, (![B_572, A_573]: (m1_subset_1(u1_struct_0(B_572), k1_zfmisc_1(u1_struct_0(A_573))) | ~m1_pre_topc(B_572, A_573) | ~l1_pre_topc(A_573))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.01/1.62  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.01/1.62  tff(c_194, plain, (![A_580, A_581, B_582]: (m1_subset_1(A_580, u1_struct_0(A_581)) | ~r2_hidden(A_580, u1_struct_0(B_582)) | ~m1_pre_topc(B_582, A_581) | ~l1_pre_topc(A_581))), inference(resolution, [status(thm)], [c_154, c_10])).
% 4.01/1.62  tff(c_200, plain, (![A_583, A_584, B_585]: (m1_subset_1(A_583, u1_struct_0(A_584)) | ~m1_pre_topc(B_585, A_584) | ~l1_pre_topc(A_584) | v1_xboole_0(u1_struct_0(B_585)) | ~m1_subset_1(A_583, u1_struct_0(B_585)))), inference(resolution, [status(thm)], [c_8, c_194])).
% 4.01/1.62  tff(c_204, plain, (![A_583]: (m1_subset_1(A_583, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_583, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_66, c_200])).
% 4.01/1.62  tff(c_212, plain, (![A_583]: (m1_subset_1(A_583, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_583, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_204])).
% 4.01/1.62  tff(c_219, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_212])).
% 4.01/1.62  tff(c_18, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.01/1.62  tff(c_222, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_219, c_18])).
% 4.01/1.62  tff(c_225, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_222])).
% 4.01/1.62  tff(c_233, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_225])).
% 4.01/1.62  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_233])).
% 4.01/1.62  tff(c_239, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_212])).
% 4.01/1.62  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.62  tff(c_377, plain, (![C_631, A_632, B_633, D_634]: (m1_connsp_2(C_631, A_632, B_633) | ~r2_hidden(B_633, D_634) | ~r1_tarski(D_634, C_631) | ~v3_pre_topc(D_634, A_632) | ~m1_subset_1(D_634, k1_zfmisc_1(u1_struct_0(A_632))) | ~m1_subset_1(C_631, k1_zfmisc_1(u1_struct_0(A_632))) | ~m1_subset_1(B_633, u1_struct_0(A_632)) | ~l1_pre_topc(A_632) | ~v2_pre_topc(A_632) | v2_struct_0(A_632))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.01/1.62  tff(c_399, plain, (![C_648, A_649, A_650, B_651]: (m1_connsp_2(C_648, A_649, A_650) | ~r1_tarski(B_651, C_648) | ~v3_pre_topc(B_651, A_649) | ~m1_subset_1(B_651, k1_zfmisc_1(u1_struct_0(A_649))) | ~m1_subset_1(C_648, k1_zfmisc_1(u1_struct_0(A_649))) | ~m1_subset_1(A_650, u1_struct_0(A_649)) | ~l1_pre_topc(A_649) | ~v2_pre_topc(A_649) | v2_struct_0(A_649) | v1_xboole_0(B_651) | ~m1_subset_1(A_650, B_651))), inference(resolution, [status(thm)], [c_8, c_377])).
% 4.01/1.62  tff(c_407, plain, (![B_655, A_656, A_657]: (m1_connsp_2(B_655, A_656, A_657) | ~v3_pre_topc(B_655, A_656) | ~m1_subset_1(B_655, k1_zfmisc_1(u1_struct_0(A_656))) | ~m1_subset_1(A_657, u1_struct_0(A_656)) | ~l1_pre_topc(A_656) | ~v2_pre_topc(A_656) | v2_struct_0(A_656) | v1_xboole_0(B_655) | ~m1_subset_1(A_657, B_655))), inference(resolution, [status(thm)], [c_6, c_399])).
% 4.01/1.62  tff(c_413, plain, (![B_47, A_45, A_657]: (m1_connsp_2(u1_struct_0(B_47), A_45, A_657) | ~v3_pre_topc(u1_struct_0(B_47), A_45) | ~m1_subset_1(A_657, u1_struct_0(A_45)) | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | v1_xboole_0(u1_struct_0(B_47)) | ~m1_subset_1(A_657, u1_struct_0(B_47)) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_36, c_407])).
% 4.01/1.62  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_82, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_90, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 4.01/1.62  tff(c_146, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 4.01/1.62  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_286])).
% 4.01/1.62  tff(c_89, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_88])).
% 4.01/1.62  tff(c_199, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_146, c_89])).
% 4.01/1.62  tff(c_424, plain, (![D_674, E_677, C_673, A_678, H_676, F_675, B_679]: (r1_tmap_1(D_674, B_679, E_677, H_676) | ~r1_tmap_1(C_673, B_679, k3_tmap_1(A_678, B_679, D_674, C_673, E_677), H_676) | ~m1_connsp_2(F_675, D_674, H_676) | ~r1_tarski(F_675, u1_struct_0(C_673)) | ~m1_subset_1(H_676, u1_struct_0(C_673)) | ~m1_subset_1(H_676, u1_struct_0(D_674)) | ~m1_subset_1(F_675, k1_zfmisc_1(u1_struct_0(D_674))) | ~m1_pre_topc(C_673, D_674) | ~m1_subset_1(E_677, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_674), u1_struct_0(B_679)))) | ~v1_funct_2(E_677, u1_struct_0(D_674), u1_struct_0(B_679)) | ~v1_funct_1(E_677) | ~m1_pre_topc(D_674, A_678) | v2_struct_0(D_674) | ~m1_pre_topc(C_673, A_678) | v2_struct_0(C_673) | ~l1_pre_topc(B_679) | ~v2_pre_topc(B_679) | v2_struct_0(B_679) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(cnfTransformation, [status(thm)], [f_235])).
% 4.01/1.62  tff(c_428, plain, (![F_675]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_675, '#skF_5', '#skF_8') | ~r1_tarski(F_675, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_675, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_199, c_424])).
% 4.01/1.62  tff(c_435, plain, (![F_675]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_675, '#skF_5', '#skF_8') | ~r1_tarski(F_675, u1_struct_0('#skF_4')) | ~m1_subset_1(F_675, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_58, c_56, c_52, c_91, c_48, c_428])).
% 4.01/1.62  tff(c_437, plain, (![F_680]: (~m1_connsp_2(F_680, '#skF_5', '#skF_8') | ~r1_tarski(F_680, u1_struct_0('#skF_4')) | ~m1_subset_1(F_680, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_146, c_435])).
% 4.01/1.62  tff(c_445, plain, (![B_47]: (~m1_connsp_2(u1_struct_0(B_47), '#skF_5', '#skF_8') | ~r1_tarski(u1_struct_0(B_47), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_47, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_437])).
% 4.01/1.62  tff(c_453, plain, (![B_681]: (~m1_connsp_2(u1_struct_0(B_681), '#skF_5', '#skF_8') | ~r1_tarski(u1_struct_0(B_681), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_681, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_445])).
% 4.01/1.62  tff(c_457, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_453])).
% 4.01/1.62  tff(c_460, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_457])).
% 4.01/1.62  tff(c_463, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_413, c_460])).
% 4.01/1.62  tff(c_466, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_52, c_48, c_145, c_91, c_463])).
% 4.01/1.62  tff(c_467, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_239, c_64, c_466])).
% 4.01/1.62  tff(c_470, plain, (~v1_tsep_1('#skF_4', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_266, c_467])).
% 4.01/1.62  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_52, c_145, c_54, c_470])).
% 4.01/1.62  tff(c_476, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.01/1.62  tff(c_730, plain, (![C_763, D_761, A_764, G_762, B_760, E_765]: (r1_tmap_1(D_761, B_760, k3_tmap_1(A_764, B_760, C_763, D_761, E_765), G_762) | ~r1_tmap_1(C_763, B_760, E_765, G_762) | ~m1_pre_topc(D_761, C_763) | ~m1_subset_1(G_762, u1_struct_0(D_761)) | ~m1_subset_1(G_762, u1_struct_0(C_763)) | ~m1_subset_1(E_765, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_763), u1_struct_0(B_760)))) | ~v1_funct_2(E_765, u1_struct_0(C_763), u1_struct_0(B_760)) | ~v1_funct_1(E_765) | ~m1_pre_topc(D_761, A_764) | v2_struct_0(D_761) | ~m1_pre_topc(C_763, A_764) | v2_struct_0(C_763) | ~l1_pre_topc(B_760) | ~v2_pre_topc(B_760) | v2_struct_0(B_760) | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.01/1.62  tff(c_732, plain, (![D_761, A_764, G_762]: (r1_tmap_1(D_761, '#skF_3', k3_tmap_1(A_764, '#skF_3', '#skF_5', D_761, '#skF_6'), G_762) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_762) | ~m1_pre_topc(D_761, '#skF_5') | ~m1_subset_1(G_762, u1_struct_0(D_761)) | ~m1_subset_1(G_762, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_761, A_764) | v2_struct_0(D_761) | ~m1_pre_topc('#skF_5', A_764) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(resolution, [status(thm)], [c_56, c_730])).
% 4.01/1.62  tff(c_735, plain, (![D_761, A_764, G_762]: (r1_tmap_1(D_761, '#skF_3', k3_tmap_1(A_764, '#skF_3', '#skF_5', D_761, '#skF_6'), G_762) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_762) | ~m1_pre_topc(D_761, '#skF_5') | ~m1_subset_1(G_762, u1_struct_0(D_761)) | ~m1_subset_1(G_762, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_761, A_764) | v2_struct_0(D_761) | ~m1_pre_topc('#skF_5', A_764) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_58, c_732])).
% 4.01/1.62  tff(c_755, plain, (![D_791, A_792, G_793]: (r1_tmap_1(D_791, '#skF_3', k3_tmap_1(A_792, '#skF_3', '#skF_5', D_791, '#skF_6'), G_793) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_793) | ~m1_pre_topc(D_791, '#skF_5') | ~m1_subset_1(G_793, u1_struct_0(D_791)) | ~m1_subset_1(G_793, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_791, A_792) | v2_struct_0(D_791) | ~m1_pre_topc('#skF_5', A_792) | ~l1_pre_topc(A_792) | ~v2_pre_topc(A_792) | v2_struct_0(A_792))), inference(negUnitSimplification, [status(thm)], [c_74, c_64, c_735])).
% 4.01/1.62  tff(c_475, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.01/1.62  tff(c_760, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_755, c_475])).
% 4.01/1.62  tff(c_767, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_91, c_48, c_52, c_476, c_760])).
% 4.01/1.62  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_68, c_767])).
% 4.01/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.62  
% 4.01/1.62  Inference rules
% 4.01/1.62  ----------------------
% 4.01/1.62  #Ref     : 0
% 4.01/1.62  #Sup     : 130
% 4.01/1.62  #Fact    : 0
% 4.01/1.62  #Define  : 0
% 4.01/1.62  #Split   : 7
% 4.01/1.62  #Chain   : 0
% 4.01/1.62  #Close   : 0
% 4.01/1.62  
% 4.01/1.62  Ordering : KBO
% 4.01/1.62  
% 4.01/1.62  Simplification rules
% 4.01/1.62  ----------------------
% 4.01/1.62  #Subsume      : 17
% 4.01/1.62  #Demod        : 136
% 4.01/1.62  #Tautology    : 31
% 4.01/1.62  #SimpNegUnit  : 18
% 4.01/1.62  #BackRed      : 0
% 4.01/1.62  
% 4.01/1.62  #Partial instantiations: 0
% 4.01/1.62  #Strategies tried      : 1
% 4.01/1.62  
% 4.01/1.62  Timing (in seconds)
% 4.01/1.62  ----------------------
% 4.01/1.62  Preprocessing        : 0.41
% 4.01/1.62  Parsing              : 0.20
% 4.01/1.62  CNF conversion       : 0.07
% 4.01/1.62  Main loop            : 0.43
% 4.01/1.62  Inferencing          : 0.17
% 4.01/1.62  Reduction            : 0.12
% 4.01/1.62  Demodulation         : 0.09
% 4.01/1.62  BG Simplification    : 0.03
% 4.01/1.62  Subsumption          : 0.09
% 4.01/1.62  Abstraction          : 0.02
% 4.01/1.62  MUC search           : 0.00
% 4.01/1.62  Cooper               : 0.00
% 4.01/1.62  Total                : 0.89
% 4.01/1.63  Index Insertion      : 0.00
% 4.01/1.63  Index Deletion       : 0.00
% 4.01/1.63  Index Matching       : 0.00
% 4.01/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
